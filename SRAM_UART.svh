interface SRAM_UART_if ();
    reg ce_n;
    reg oe_n;
    reg we_n;
    reg [3:0] be_n;
    reg [19:0] addr;
    reg [31:0] data;
    
    reg rdn;         //读串口信号，低有效
    reg wrn;         //写串口信号，低有效
    wire dataready;    //串口数据准备好
    wire tbre;         //发送数据标志
    wire tsre;         //数据发送完毕标志
    
    modport client (
        output ce_n, oe_n, we_n, be_n, addr,
        inout data,
        
        output rdn, wrn,
        input dataready, tbre, tsre,
        
        export task SRAM_reset(),
        
        export task SRAM_request_read(),
        export task SRAM_read(),
        export task SRAM_read_byte_signed(),
        
        export task SRAM_prepare_write(),
        export task SRAM_prepare_write_byte(),
        export task SRAM_start_write(),
        export task SRAM_end_write(),
        
        export task UART_reset(),
        
        export task UART_request_read(),
        export function UART_has_data(),
        export task UART_read(),
        export task UART_read_signed(),
        
        export task UART_request_write(),
        export function UART_has_written(),
        export task UART_end_write()
    );
    
    // ========================
    // SRAM
    
    // Reset
    
    task SRAM_reset();
        ce_n <= 1;
        oe_n <= 1;
        we_n <= 1;
        be_n <= 4'b0000;
    endtask
    
    // Read
    
    task SRAM_request_read(input logic [19:0] in_addr, input logic [3:0] in_be_n);
        addr <= in_addr;
        be_n <= in_be_n;
        ce_n <= 0;
        oe_n <= 0;
        data <= 32'bzzzzzzzz_zzzzzzzz_zzzzzzzz_zzzzzzzz;
    endtask
        
    task SRAM_read(output logic [31:0] out_data);
        out_data <= data;
        ce_n <= 1;
        oe_n <= 1;
    endtask
    
    task SRAM_read_byte_signed(output logic [31:0] out_data, input logic [1:0] byte_index);
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
    
    task SRAM_prepare_write(input logic [19:0] in_addr, input logic [3:0] in_be_n,
        input logic [31:0] in_data);
        addr <= in_addr;
        be_n <= in_be_n;
        data <= in_data;
    endtask
    
    task SRAM_prepare_write_byte(input logic [19:0] in_addr, input logic [1:0] byte_index,
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
    
    task SRAM_start_write();
        ce_n <= 0;
        we_n <= 0;
    endtask
    
    task SRAM_end_write();
        ce_n <= 1;
        we_n <= 1;
    endtask
    
    // ========================
    // UART
    
    reg is_reading = 0;
    reg is_writing = 0;
    reg has_tbre = 0;
    reg has_tsre = 0;
    
    // Reset
    
    task UART_reset();
        rdn <= 1;
        wrn <= 1;
        is_reading <= 0;
        is_writing <= 0;
        has_tbre <= 0;
        has_tsre <= 0;
    endtask
    
    // Read
    
    task UART_request_read();
        if (!is_reading && dataready) begin
            is_reading <= 1;
            rdn <= 0;
            data[7:0] <= 8'bzzzzzzzz;
        end
    endtask
    
    function UART_has_data();
        return is_reading;
    endfunction
    
    task UART_read(output logic [7:0] out_data);
        rdn <= 1;
        out_data <= data[7:0];
        is_reading <= 0;
    endtask
    
    task UART_read_signed(output logic [31:0] out_data);
        rdn <= 1;
        out_data <= { {24 {data[7]}}, data[7:0] };
        is_reading <= 0;
    endtask
    
    // Write
    
    task UART_request_write(input logic [7:0] in_data);
        if (!is_writing) begin
            is_writing <= 1;
            wrn <= 0;
            data[7:0] <= in_data;
        end else if (is_writing && !wrn) begin
            wrn <= 1;
        end else if (is_writing && wrn && !has_tbre && tbre) begin
            has_tbre <= 1;
        end else if (is_writing && wrn && has_tbre && !has_tsre && tsre) begin
            has_tsre <= 1;
        end
    endtask
    
    function UART_has_written();
        return is_writing && has_tsre;
    endfunction
    
    task UART_end_write();
        is_writing <= 0;
        has_tbre <= 0;
        has_tsre <= 0;
    endtask
    
endinterface
