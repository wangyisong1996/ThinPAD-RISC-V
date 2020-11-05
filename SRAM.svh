interface SRAM_if ();
    reg ce_n;
    reg oe_n;
    reg we_n;
    reg [3:0] be_n;
    reg [19:0] addr;
    reg [31:0] data;
    
    modport client (
        output ce_n, oe_n, we_n, be_n, addr,
        inout data,
        
        export task reset(),
        
        export task request_read(),
        export task read(),
        export task read_byte_signed(),
        
        export task prepare_write(),
        export task prepare_write_byte(),
        export task start_write(),
        export task end_write()
    );
    
    // Reset
    
    task reset();
        ce_n <= 1;
        oe_n <= 1;
        we_n <= 1;
        be_n <= 4'b0000;
    endtask
    
    // Read
    
    task request_read(input logic [19:0] in_addr, input logic [3:0] in_be_n);
        addr <= in_addr;
        be_n <= in_be_n;
        ce_n <= 0;
        oe_n <= 0;
        data <= 32'bzzzzzzzz_zzzzzzzz_zzzzzzzz_zzzzzzzz;
    endtask
        
    task read(output logic [31:0] out_data);
        out_data <= data;
        ce_n <= 1;
        oe_n <= 1;
    endtask
    
    task read_byte_signed(output logic [31:0] out_data, input logic [1:0] byte_index);
        case (byte_index)
            2'd0: out_data <= { {24 {data[7]}}, data[7:0] };
            2'd1: out_data <= { {24 {data[15]}}, data[15:8] };
            2'd2: out_data <= { {24 {data[22]}}, data[23:16] };
            2'd3: out_data <= { {24 {data[31]}}, data[31:24] };
        endcase
        ce_n <= 1;
        oe_n <= 1;
    endtask
    
    // Write
    
    task prepare_write(input logic [19:0] in_addr, input logic [3:0] in_be_n,
        input logic [31:0] in_data);
        addr <= in_addr;
        be_n <= in_be_n;
        data <= in_data;
    endtask
    
    task prepare_write_byte(input logic [19:0] in_addr, input logic [1:0] byte_index,
        input logic [7:0] in_data);
        addr <= in_addr;
        
        be_n[0] <= byte_index != 0;
        be_n[1] <= byte_index != 1;
        be_n[2] <= byte_index != 2;
        be_n[3] <= byte_index != 3;
        
        data <= 32'h0;
        case (byte_index)
            2'd0: data[7:0] <= in_data;
            2'd1: data[15:8] <= in_data;
            2'd2: data[23:16] <= in_data;
            2'd3: data[31:24] <= in_data;
        endcase
    endtask
    
    task start_write();
        ce_n <= 0;
        we_n <= 0;
    endtask
    
    task end_write();
        ce_n <= 1;
        we_n <= 1;
    endtask
    
endinterface
