module MultiCycleCPU(base_ram, ext_ram, clk, reset, pc_out, addr_out);

`include "SRAM_UART.svh"
`include "SRAM.svh"

SRAM_UART_if.client base_ram;
SRAM_if.client ext_ram;
input wire clk;
input wire reset;
output reg [31:0] pc_out = 0;
output wire [31:0] addr_out;

enum {
	S_RESET,
	S_IF,
	S_ID,
	S_EXE,
	S_ERROR
} cpu_state = S_RESET;

typedef enum {
	U_READ_RS1,
	U_READ_RS1_RS2,
	U_READ_PC_AS_RS1,
	U_READ_NPC_AS_RD,
	U_ALU_ADD,
	U_ALU_AND,
	U_ALU_OR,
	U_ALU_XOR,
	U_ALU_EQ,
	U_ALU_NE,
	U_ALU_ADD_IMM,
	U_ALU_AND_IMM,
	U_ALU_OR_IMM,
	U_ALU_SLL_IMM,
	U_ALU_SRL_IMM,
	U_LOAD_WORD,
	U_LOAD_BYTE,
	U_STORE_WORD,
	U_STORE_BYTE,
	U_WRITE_RD,
	U_BRANCH_COND,
	U_BRANCH_ALWAYS,
	U_BRANCH_JALR,
	U_READ_UART,
	U_WRITE_UART,
	U_NOP,
	U_ERROR
} uop_t;

uop_t uops[0:3] = '{4 {U_NOP}};
reg [31:0] pc = 0;
reg [31:0] insn;
reg [31:0] orig_pc;
reg [4:0] rs1;
reg [4:0] rs2;
reg [4:0] rd;
reg [31:0] imm;
reg [31:0] rs1_value;
reg [31:0] rs2_value;
reg [31:0] rd_value;

wire [4:0] regs_idx_write;
wire [31:0] regs_data_write;
wire [31:0] regs_data_read_1;
wire [31:0] regs_data_read_2;

assign regs_idx_write = uops[0] == U_WRITE_RD ? rd : 0;
assign regs_data_write = rd_value;

SimpleRegisterFile regs (
	.idx_write(regs_idx_write),
	.data_write(regs_data_write),
	.idx_read_1(rs1),
	.data_read_1(regs_data_read_1),
	.idx_read_2(rs2),
	.data_read_2(regs_data_read_2),
	.clk(clk),
	.reset(reset),
	.debug_out()
);

enum {
	SR_IDLE,
	SR_READ_REQUESTED,
	SR_WRITE_PREPARED,
	SR_WRITE_STARTED
} sram_state = SR_IDLE;

localparam SRAM_DELAY_CYCLES = 4;
reg [2:0] cycles_remaining;

localparam UART_DELAY_CYCLES = 10;
reg [3:0] uart_cycles;

// UART Range: 0x10000000 ~ 0x10000007
localparam UART_ADDR_PREFIX = 32'h10000000;
localparam UART_DATA_ADDR = 32'h10000000;
localparam UART_STATUS_ADDR = 32'h10000005;

function is_uart_addr(logic [31:0] addr);
	return addr[31:3] == UART_ADDR_PREFIX[31:3];
endfunction

always_ff @ (posedge clk or posedge reset) begin
	if (reset) begin
		do_RESET();
	end else begin
		case (cpu_state)
			S_RESET: do_RESET();
			S_IF: do_IF();
			S_ID: do_ID();
			S_EXE: do_EXE();
			S_ERROR: do_ERROR();
			default: do_ERROR();
		endcase
	end
end

reg is_first_char;  // for \x0c

task do_RESET();
	pc_out <= 0;
	
	base_ram.UART_reset();
	base_ram.SRAM_reset();
	ext_ram.reset();
	sram_state <= SR_IDLE;
	cycles_remaining <= 1;
	uart_cycles <= 1;
	
	is_first_char <= 1;
	
	uops <= '{4 {U_NOP}};
	pc <= 32'h80000000;
	
	cpu_state <= S_IF;
endtask


function is_base_ram_addr(logic [31:0] addr);
	// 0x800 ~ 0x804
	return addr[31:24] == 8'h80 && addr[23:22] == 2'b00;
endfunction

function is_ext_ram_addr(logic [31:0] addr);
	// 0x804 ~ 0x800
	return addr[31:24] == 8'h80 && addr[23:22] == 2'b01;
endfunction

function is_base_ram_word_aligned_addr(logic [31:0] addr);
	return is_base_ram_addr(addr) && addr[1:0] == 2'b00;
endfunction

function is_ext_ram_word_aligned_addr(logic [31:0] addr);
	return is_ext_ram_addr(addr) && addr[1:0] == 2'b00;
endfunction

enum reg { SR_BASE_RAM, SR_EXT_RAM } sram_access;
reg [1:0] sram_byte_index;

task do_IF();
	// instruction = M[pc]; orig_pc = pc; pc += 4;
	
	if (sram_state == SR_IDLE) begin
		pc_out <= pc;
		
		if (is_base_ram_word_aligned_addr(pc)) begin
			base_ram.SRAM_request_read(pc[21:2], 4'b0000);
			sram_state <= SR_READ_REQUESTED;
			sram_access <= SR_BASE_RAM;
			cycles_remaining <= SRAM_DELAY_CYCLES;
		end else if (is_ext_ram_word_aligned_addr(pc)) begin
			ext_ram.request_read(pc[21:2], 4'b0000);
			sram_state <= SR_READ_REQUESTED;
			sram_access <= SR_EXT_RAM;
			cycles_remaining <= SRAM_DELAY_CYCLES;
		end else begin
			cpu_state <= S_ERROR;
		end
	end else if (sram_state == SR_READ_REQUESTED) begin
		if (cycles_remaining == 1) begin
			if (sram_access == SR_BASE_RAM) begin
				base_ram.SRAM_read(insn);
			end else begin
				ext_ram.read(insn);
			end
			orig_pc <= pc;
			pc <= pc + 4;
			sram_state <= SR_IDLE;
			cpu_state <= S_ID;
		end else begin
			cycles_remaining <= cycles_remaining - 1;
		end
	end else begin
		// error state??
		cpu_state <= S_ERROR;
	end
endtask

// for ID
wire [6:0] funct7 = insn[31:25];
wire [2:0] funct3 = insn[14:12];
wire [6:0] opcode = insn[6:0];
wire [4:0] insn_rs1 = insn[19:15];
wire [4:0] insn_rs2 = insn[24:20];
wire [4:0] insn_rd = insn[11:7];
wire [4:0] insn_shamt32 = insn[24:20];
wire [11:0] imm_I = insn[31:20];
wire [11:0] imm_S = { insn[31:25], insn[11:7] };
wire [11:0] imm_B = { insn[31], insn[7], insn[30:25], insn[11:8] };
wire [19:0] imm_U = insn[31:12];
wire [19:0] imm_J = { insn[31], insn[19:12], insn[20], insn[30:21] };
wire [31:0] imm_I_sext = { {20 {imm_I[11]}}, imm_I };
wire [31:0] imm_S_sext = { {20 {imm_S[11]}}, imm_S };
wire [31:0] imm_B_sext = { {19 {imm_B[11]}}, imm_B, 1'b0 };
wire [31:0] imm_U_sext = { imm_U, 12'h0 };
wire [31:0] imm_J_sext = { {11 {imm_J[19]}}, imm_J, 1'b0 };

task do_ID();
	// (rs1, rs2, rd, imm) = extract(insn); set_uops(insn);
	
	rs1 <= insn_rs1;
	rs2 <= insn_rs2;
	rd <= insn_rd;
	
	cpu_state <= S_EXE;
	uops[0] <= U_ERROR;
	
	do_ID_add();
	do_ID_addi();
	do_ID_and();
	do_ID_andi();
	do_ID_auipc();
	do_ID_beq();
	do_ID_bne();
	do_ID_jal();
	do_ID_jalr();
	do_ID_lb();
	do_ID_lui();
	do_ID_lw();
	do_ID_or();
	do_ID_ori();
	do_ID_sb();
	do_ID_slli();
	do_ID_srli();
	do_ID_sw();
	do_ID_xor();
endtask

task do_ID_add();
	if (opcode == 7'b0110011 && funct3 == 3'b000 && funct7 == 0) begin
		uops <= { U_READ_RS1_RS2, U_ALU_ADD, U_WRITE_RD, U_NOP };
	end
endtask

task do_ID_addi();
	if (opcode == 7'b0010011 && funct3 == 3'b000) begin
		imm <= imm_I_sext;
		uops <= { U_READ_RS1, U_ALU_ADD_IMM, U_WRITE_RD, U_NOP };
	end
endtask

task do_ID_and();
	if (opcode == 7'b0110011 && funct3 == 3'b111 && funct7 == 0) begin
		uops <= { U_READ_RS1_RS2, U_ALU_AND, U_WRITE_RD, U_NOP };
	end
endtask

task do_ID_andi();
	if (opcode == 7'b0010011 && funct3 == 3'b111) begin
		imm <= imm_I_sext;
		uops <= { U_READ_RS1, U_ALU_AND_IMM, U_WRITE_RD, U_NOP };
	end
endtask

task do_ID_auipc();
	if (opcode == 7'b0010111) begin
		imm <= imm_U_sext;
		uops <= { U_READ_PC_AS_RS1, U_ALU_ADD_IMM, U_WRITE_RD, U_NOP };
	end
endtask

task do_ID_beq();
	if (opcode == 7'b1100011 && funct3 == 3'b000) begin
		imm <= imm_B_sext;
		uops <= { U_READ_RS1_RS2, U_ALU_EQ, U_BRANCH_COND, U_NOP };
	end
endtask

task do_ID_bne();
	if (opcode == 7'b1100011 && funct3 == 3'b001) begin
		imm <= imm_B_sext;
		uops <= { U_READ_RS1_RS2, U_ALU_NE, U_BRANCH_COND, U_NOP };
	end
endtask

task do_ID_jal();
	if (opcode == 7'b1101111) begin
		imm <= imm_J_sext;
		uops <= { U_READ_NPC_AS_RD, U_WRITE_RD, U_BRANCH_ALWAYS, U_NOP };
		
		// Special case: j
		if (insn_rd == 0) begin
			uops <= { U_BRANCH_ALWAYS, U_NOP, U_NOP, U_NOP };
		end
	end
endtask

task do_ID_jalr();
	if (opcode == 7'b1100111 && funct3 == 3'b000) begin
		imm <= imm_I_sext;
		uops <= { U_READ_RS1, U_BRANCH_JALR, U_READ_NPC_AS_RD, U_WRITE_RD };
		
		// Special case: jr
		if (insn_rd == 0) begin
			uops <= { U_READ_RS1, U_BRANCH_JALR, U_NOP, U_NOP };
		end
	end
endtask

task do_ID_lb();
	if (opcode == 7'b0000011 && funct3 == 3'b000) begin
		imm <= imm_I_sext;
		uops <= { U_READ_RS1, U_ALU_ADD_IMM, U_LOAD_BYTE, U_WRITE_RD };
	end
endtask

task do_ID_lui();
	if (opcode == 7'b0110111) begin
		rd_value <= imm_U_sext;
		uops <= { U_WRITE_RD, U_NOP, U_NOP, U_NOP };
	end
endtask

task do_ID_lw();
	if (opcode == 7'b0000011 && funct3 == 3'b010) begin
		imm <= imm_I_sext;
		uops <= { U_READ_RS1, U_ALU_ADD_IMM, U_LOAD_WORD, U_WRITE_RD };
	end
endtask

task do_ID_or();
	if (opcode == 7'b0110011 && funct3 == 3'b110 && funct7 == 0) begin
		uops <= { U_READ_RS1_RS2, U_ALU_OR, U_WRITE_RD, U_NOP };
	end
endtask

task do_ID_ori();
	if (opcode == 7'b0010011 && funct3 == 3'b110) begin
		imm <= imm_I_sext;
		uops <= { U_READ_RS1, U_ALU_OR_IMM, U_WRITE_RD, U_NOP };
	end
endtask

task do_ID_sb();
	if (opcode == 7'b0100011 && funct3 == 3'b000) begin
		imm <= imm_S_sext;
		uops <= { U_READ_RS1_RS2, U_ALU_ADD_IMM, U_STORE_BYTE, U_NOP };
	end
endtask

task do_ID_slli();
	if (opcode == 7'b0010011 && funct3 == 3'b001 && funct7 == 0) begin
		imm <= insn_shamt32;
		uops <= { U_READ_RS1, U_ALU_SLL_IMM, U_WRITE_RD, U_NOP };
	end
endtask

task do_ID_srli();
	if (opcode == 7'b0010011 && funct3 == 3'b101 && funct7 == 0) begin
		imm <= insn_shamt32;
		uops <= { U_READ_RS1, U_ALU_SRL_IMM, U_WRITE_RD, U_NOP };
	end
endtask

task do_ID_sw();
	if (opcode == 7'b0100011 && funct3 == 3'b010) begin
		imm <= imm_S_sext;
		uops <= { U_READ_RS1_RS2, U_ALU_ADD_IMM, U_STORE_WORD, U_NOP };
	end
endtask

task do_ID_xor();
	if (opcode == 7'b0110011 && funct3 == 3'b100 && funct7 == 0) begin
		uops <= { U_READ_RS1_RS2, U_ALU_XOR, U_WRITE_RD, U_NOP };
	end
endtask


task do_EXE();
	uops <= { uops[1:3], U_NOP };
	
	case (uops[0])
		U_READ_RS1: do_read_rs1();
		U_READ_RS1_RS2: do_read_rs1_rs2();
		U_READ_PC_AS_RS1: do_read_pc_as_rs1();
		U_READ_NPC_AS_RD: do_read_npc_as_rd();
		U_ALU_ADD: do_alu_add();
		U_ALU_AND: do_alu_and();
		U_ALU_OR: do_alu_or();
		U_ALU_XOR: do_alu_xor();
		U_ALU_EQ: do_alu_eq();
		U_ALU_NE: do_alu_ne();
		U_ALU_ADD_IMM: do_alu_add_imm();
		U_ALU_AND_IMM: do_alu_and_imm();
		U_ALU_OR_IMM: do_alu_or_imm();
		U_ALU_SLL_IMM: do_alu_sll_imm();
		U_ALU_SRL_IMM: do_alu_srl_imm();
		U_LOAD_WORD: do_load_word();
		U_LOAD_BYTE: do_load_byte();
		U_STORE_WORD: do_store_word();
		U_STORE_BYTE: do_store_byte();
		U_WRITE_RD: do_write_rd();
		U_BRANCH_COND: do_branch_cond();
		U_BRANCH_ALWAYS: do_branch_always();
		U_BRANCH_JALR: do_branch_jalr();
		U_READ_UART: do_read_uart();
		U_WRITE_UART: do_write_uart();
		U_NOP: cpu_state <= S_IF;
		default: cpu_state <= S_ERROR;
	endcase
endtask

task uop_not_finished();
	uops <= uops;
endtask

task do_read_rs1();
	rs1_value <= regs_data_read_1;
endtask

task do_read_rs1_rs2();
	rs1_value <= regs_data_read_1;
	rs2_value <= regs_data_read_2;
endtask

task do_read_pc_as_rs1();
	rs1_value <= orig_pc;
endtask

task do_read_npc_as_rd();
	rd_value <= orig_pc + 4;
endtask

task do_alu_add();
	rd_value <= rs1_value + rs2_value;
endtask

task do_alu_and();
	rd_value <= rs1_value & rs2_value;
endtask

task do_alu_or();
	rd_value <= rs1_value | rs2_value;
endtask

task do_alu_xor();
	rd_value <= rs1_value ^ rs2_value;
endtask

task do_alu_eq();
	rd_value[31:1] <= 0;
	rd_value[0] <= rs1_value == rs2_value;
endtask

task do_alu_ne();
	rd_value[31:1] <= 0;
	rd_value[0] <= rs1_value != rs2_value;
endtask

task do_alu_add_imm();
	rd_value <= rs1_value + imm;
endtask

task do_alu_and_imm();
	rd_value <= rs1_value & imm;
endtask

task do_alu_or_imm();
	rd_value <= rs1_value | imm;
endtask

task do_alu_sll_imm();
	rd_value <= rs1_value << imm[4:0];
endtask

task do_alu_srl_imm();
	rd_value <= rs1_value >> imm[4:0];
endtask

// for load/store
wire [31:0] mem_addr = rd_value;
wire [31:0] mem_data_to_write = rs2_value;

// debug!
// assign addr_out = mem_addr;
// assign addr_out = rs1_value;
assign addr_out = { 3'h0, rs1, 3'h0, rs2 };

task do_load_word();
	if (sram_state == SR_IDLE) begin
		if (is_base_ram_word_aligned_addr(mem_addr)) begin
			base_ram.SRAM_request_read(mem_addr[21:2], 4'b0000);
			sram_state <= SR_READ_REQUESTED;
			sram_access <= SR_BASE_RAM;
			cycles_remaining <= SRAM_DELAY_CYCLES;
			uop_not_finished();
		end else if (is_ext_ram_word_aligned_addr(mem_addr)) begin
			ext_ram.request_read(mem_addr[21:2], 4'b0000);
			sram_state <= SR_READ_REQUESTED;
			sram_access <= SR_EXT_RAM;
			cycles_remaining <= SRAM_DELAY_CYCLES;
			uop_not_finished();
		end else begin
			cpu_state <= S_ERROR;
		end
	end else if (sram_state == SR_READ_REQUESTED) begin
		if (cycles_remaining == 1) begin
			if (sram_access == SR_BASE_RAM) begin
				base_ram.SRAM_read(rd_value);
			end else begin
				ext_ram.read(rd_value);
			end
			sram_state <= SR_IDLE;
		end else begin
			cycles_remaining <= cycles_remaining - 1;
			uop_not_finished();
		end
	end else begin
		cpu_state <= S_ERROR;
	end
endtask

task do_load_byte();
	if (sram_state == SR_IDLE) begin
		if (is_base_ram_addr(mem_addr)) begin
			base_ram.SRAM_request_read(mem_addr[21:2], 4'b0000);
			sram_state <= SR_READ_REQUESTED;
			sram_access <= SR_BASE_RAM;
			sram_byte_index <= mem_addr[1:0];
			cycles_remaining <= SRAM_DELAY_CYCLES;
			uop_not_finished();
		end else if (is_ext_ram_addr(mem_addr)) begin
			ext_ram.request_read(mem_addr[21:2], 4'b0000);
			sram_state <= SR_READ_REQUESTED;
			sram_access <= SR_EXT_RAM;
			sram_byte_index <= mem_addr[1:0];
			cycles_remaining <= SRAM_DELAY_CYCLES;
			uop_not_finished();
		end else if (mem_addr == UART_DATA_ADDR) begin
			uop_not_finished();
			uops[0] <= U_READ_UART;
		end else if (mem_addr == UART_STATUS_ADDR) begin
			rd_value <= 32'h0;
			rd_value[5] <= 1;  // Always available to write
			rd_value[0] <= base_ram.dataready;
		end else if (is_uart_addr(mem_addr)) begin
			rd_value <= 32'h0;  // Got a zero!
		end else begin
			cpu_state <= S_ERROR;
		end
	end else if (sram_state == SR_READ_REQUESTED) begin
		if (cycles_remaining == 1) begin
			if (sram_access == SR_BASE_RAM) begin
				base_ram.SRAM_read_byte_signed(rd_value, sram_byte_index);
			end else begin
				ext_ram.read_byte_signed(rd_value, sram_byte_index);
			end
			sram_state <= SR_IDLE;
		end else begin
			cycles_remaining <= cycles_remaining - 1;
			uop_not_finished();
		end
	end else begin
		cpu_state <= S_ERROR;
	end
endtask

task do_store_word();
	if (sram_state == SR_IDLE) begin
		if (is_base_ram_word_aligned_addr(mem_addr)) begin
			base_ram.SRAM_prepare_write(mem_addr[21:2], 4'b0000, mem_data_to_write);
			sram_state <= SR_WRITE_PREPARED;
			sram_access <= SR_BASE_RAM;
			uop_not_finished();
		end else if (is_ext_ram_word_aligned_addr(mem_addr)) begin
			ext_ram.prepare_write(mem_addr[21:2], 4'b0000, mem_data_to_write);
			sram_state <= SR_WRITE_PREPARED;
			sram_access <= SR_EXT_RAM;
			uop_not_finished();
		end else begin
			cpu_state <= S_ERROR;
		end
	end else if (sram_state == SR_WRITE_PREPARED) begin
		if (sram_access == SR_BASE_RAM) begin
			base_ram.SRAM_start_write();
		end else begin
			ext_ram.start_write();
		end
		sram_state <= SR_WRITE_STARTED;
		cycles_remaining <= SRAM_DELAY_CYCLES;
		uop_not_finished();
	end else if (sram_state == SR_WRITE_STARTED) begin
		if (cycles_remaining == 1) begin
			if (sram_access == SR_BASE_RAM) begin
				base_ram.SRAM_end_write();
			end else begin
				ext_ram.end_write();
			end
			sram_state <= SR_IDLE;
		end else begin
			cycles_remaining <= cycles_remaining - 1;
			uop_not_finished();
		end
	end else begin
		cpu_state <= S_ERROR;
	end
endtask

task do_store_byte();
	if (sram_state == SR_IDLE) begin
		if (is_base_ram_addr(mem_addr)) begin
			base_ram.SRAM_prepare_write_byte(mem_addr[21:2], mem_addr[1:0], mem_data_to_write[7:0]);
			sram_state <= SR_WRITE_PREPARED;
			sram_access <= SR_BASE_RAM;
			uop_not_finished();
		end else if (is_ext_ram_addr(mem_addr)) begin
			ext_ram.prepare_write_byte(mem_addr[21:2], mem_addr[1:0], mem_data_to_write[7:0]);
			sram_state <= SR_WRITE_PREPARED;
			sram_access <= SR_EXT_RAM;
			uop_not_finished();
		end else if (mem_addr == UART_DATA_ADDR) begin
			uop_not_finished();
			uops[0] <= U_WRITE_UART;
		end else if (is_uart_addr(mem_addr)) begin
			// Do nothing, just wait
		end else begin
			cpu_state <= S_ERROR;
		end
	end else if (sram_state == SR_WRITE_PREPARED) begin
		if (sram_access == SR_BASE_RAM) begin
			base_ram.SRAM_start_write();
		end else begin
			ext_ram.start_write();
		end
		sram_state <= SR_WRITE_STARTED;
		cycles_remaining <= SRAM_DELAY_CYCLES;
		uop_not_finished();
	end else if (sram_state == SR_WRITE_STARTED) begin
		if (cycles_remaining == 1) begin
			if (sram_access == SR_BASE_RAM) begin
				base_ram.SRAM_end_write();
			end else begin
				ext_ram.end_write();
			end
			sram_state <= SR_IDLE;
		end else begin
			cycles_remaining <= cycles_remaining - 1;
			uop_not_finished();
		end
	end else begin
		cpu_state <= S_ERROR;
	end
endtask

task do_read_uart();
	if (uart_cycles == UART_DELAY_CYCLES) begin
		uart_cycles <= 1;
		
		if (base_ram.UART_has_data()) begin
			base_ram.UART_read_signed(rd_value);
		end else begin
			base_ram.UART_request_read();
			uop_not_finished();
		end
	end else begin
		uart_cycles <= uart_cycles + 1;
		uop_not_finished();
	end
endtask

task do_write_uart();
	if (is_first_char) begin
		is_first_char <= 0;
	end else begin
		if (uart_cycles == UART_DELAY_CYCLES) begin
			uart_cycles <= 1;
			
			if (base_ram.UART_has_written()) begin
				base_ram.UART_end_write();
			end else begin
				base_ram.UART_request_write(mem_data_to_write[7:0]);
				uop_not_finished();
			end
		end else begin
			uart_cycles <= uart_cycles + 1;
			uop_not_finished();
		end
	end
endtask

task do_write_rd();
	// Do nothing
	// Just wait for the rising edge
endtask

task do_branch_cond();
	if (rd_value[0]) pc <= orig_pc + imm;
endtask

task do_branch_always();
	pc <= orig_pc + imm;
endtask

task do_branch_jalr();
	pc <= rs1_value + imm;
	pc[0] <= 0;
endtask

task do_ERROR();
	cpu_state <= S_ERROR;
endtask

endmodule
