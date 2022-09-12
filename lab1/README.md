Exercise for lab 1 - Sequences:

Ex1:
- Create a sequence `s1` that matches if `data_avail` is high after 4 cycles when `read_req` signal asserted
- Create sequence `s2` which matches if within a range of `[1:10]` cycles after `data_avail` goes high, `data_consumed` is asserted
- Create sequence `s3` that matches if the sequence `s1` occurs 1 cycle following the sequence `s2`

Ex2:
- Create a sequence that matches when a signal is asserted for a single clock cycle or two clock cycles consecutively max
  - Pick the signal name as `signal1` and this can either go high for 1 clock or for 2 clocks only and sequence should match on both conditions.
  

Ex3:
- Create a sequence and use it to have an assertion that checks the following:
  - Once `req` is asserted, an `ack` must be asserted before another `req` is asserted again

Ex4:
- Create an assertion using a sequence that makes sure:
  - If both `fifo_write` and `fifo_read` is asserted in the same cycle then the `num_entries_fifo` doesn't change because whatever written got read


**Solution first try**:

- Ex1:
    ```sv
    sequence s1;
        @(posedge clk) read_req ##4 data_avail;
    endsequence

    sequence s2;
        @(posedge clk) data_avail ##[1:10] data_consumed;
    endsequence

    sequence s3;
        @(posedge clk) s1 ##1 s2;
    endsequence
    ```

- Ex2:
    ```sv
    sequence signal_high_two_clocks;
        @(posedge clk) signal1[*2:3];
    endsequence
    ```

- Ex3:
    ```sv
    property req_ack_required
        @(posedge clk) req |-> not(req [*1:$]) ##0 ack 
    endproperty

    assert property req_ack_required else $error("FAILED");
    ```

- Ex4:
    ```sv
    property check_num_entries;
        int local_num_entries;
        (fifo_write ##0 fifo_read, local_num_entries = num_entries_fifo) |=> num_entries_fifo == local_num_entries;
    endproperty

    assert property check_num_entries else $error("FAILED");
    ```

**Solution after answers**:
- Ex1 (the first try solution is also satisfied):
    ```sv
    sequence s1;
        @(posedge clk) read_req |-> ##4 data_avail;
    endsequence

    sequence s2;
        @(posedge clk) data_avail |-> ##[1:10] data_consumed;
    endsequence

    sequence s3;
        @(posedge clk) s1 ##1 s2;
    endsequence
    ```

- Ex2 (the first try solution is also satisfied):
    ```sv
    sequence signal_high_two_clocks;
        @(posedge clk) (signal1 ##1 signal1) or (signal1 ##1 signal1 ##1 signal1);
    endsequence
    ```

- Ex3:
    ```sv
    sequence req_ack_required
        @(posedge clk) $rose(req) |=> not (!ack[*0:$] ##1 $rose(req)); 
    endsequence

    assert sequence req_ack_required else $error("FAILED");
    ```

- Ex4:
    ```sv
    sequence check_num_entries;
        (fifo_write & fifo_read) |=> num_entries_fifo == $past(num_entries_fifo);
    endsequence

    assert sequence check_num_entries else $error("FAILED");
    ```
