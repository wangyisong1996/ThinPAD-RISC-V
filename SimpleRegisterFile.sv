module SimpleRegisterFile(
	idx_write, data_write,
	idx_read_1, data_read_1,
	idx_read_2, data_read_2,
	clk, reset,
	debug_out
);

input wire [4:0] idx_write;
input wire [31:0] data_write;
input wire [4:0] idx_read_1;
output wire [31:0] data_read_1;
input wire [4:0] idx_read_2;
output wire [31:0] data_read_2;
input wire clk;
input wire reset;
output wire [31:0] debug_out;

reg [31:0] regs[0:31] = '{32 {0}};
assign debug_out = regs[10];

assign data_read_1 = regs[idx_read_1];
assign data_read_2 = regs[idx_read_2];

genvar i;

generate
	for (i = 1; i < 32; i++) begin
		always_ff @ (posedge clk or posedge reset) begin
			if (reset) begin
				regs[i] <= 0;
			end else begin
				if (idx_write == i) regs[i] <= data_write;
			end
		end
	end
endgenerate

endmodule
