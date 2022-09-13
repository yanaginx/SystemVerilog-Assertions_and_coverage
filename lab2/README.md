Exercise for lab 2 - Assertions:

Ex1:
- Write an immediate assertion that checks that the `read_en` and `write_en` signal for an SRAM are mutually exclusive (both cannot be enable at the same time)

Ex2: For a 32 bit deep FIFO - write assertions for following rules/properties:
- Once `reset` is de-asserted, the `readPointer` and `writePointer` are zero and the `empty` signal is high and `full` signal is low
- FIFO `full` signal is never asserted if the `count` of entries is less than max entries in FIFO
- FIFO `full` signal gets asserted when the `count` reaches maximum entries in FIFO
- Use signals `full`, `empty`, `count` 

Ex3: 
Create an assertion to make sure that once an address is looked up in a set-associative cache - it only matches at most one set in the cache
- Assume there are 32 sets and the signal `setValid[31:0]` indicates the look up results
- Assume the signal `addressLookUp` is pulsed followed by a cycle `lookupDone` and `setValid[31:0]` has results

Ex4:
Create a property that checks that a signal is asserted for no more than 2 consecutive cycles
- Assume signal name is `sig1` and it can never be high for more than 2 cycles.


**Solution first try**:

Ex1:
```sv
assert !(read_en && write_en) else $error("read_en and write_en cannot be high at the same time");
```

Ex2:
```sv
property de_assert_rst;
    @(posedge clk) 
    !reset |-> (readPointer == 0 && writePointer == 0 && empty && !full);
endproperty : de_assert_rst

property not_assert_full_when_not_full;
    @(posedge clk)
    count < MAX_ENTRIES |-> !full;
endproperty : not_assert_full_when_not_full

property assert_full_when_full;
    @(posedge clk)
    count == MAX_ENTRIES |-> full;
endproperty : assert_full_when_full

assert de_assert_rst else $error("");
assert not_assert_full_when_not_full else $error("");
assert assert_full_when_full else $error("");
```

Ex3:
```sv
property only_1_set_valid_check;
    @(posedge clk)
    addressLookup |=> lookupDone && ($countones(setValid) == 1);
endproperty : only_1_set_valid_check;

ERROR_only_1_set_valid_check: assert property(only_1_set_valid_check) else $error("");

```

Ex4:
```sv
property sig1_high_only_2_cycles_check;
    @(posedge clk)
    sig1[*2] AND not sig1[*3:$];
endproperty : sig1_high_only_2_cycles_check;
```

**Solution after correction**:
Ex1:
```sv
assert property (@(posedge clk) not (read_en & write_en)) 
    else $error("read_en and write_en cannot be high at the same time");
```

Ex2: 
> Wrap the property name inside the property keyword and () when using in `assert`
>
> The implementation is okay, just fix the naming

```sv
property de_assert_rst;
    @(posedge clk) 
    !reset |-> (readPointer == 0 && 
                writePointer == 0 && 
                empty == 1 && 
                full == 0 &&
                count == 0);
endproperty : de_assert_rst

property fifo_not_full_check;
    @(posedge clk)
    count < MAX_ENTRIES |-> !full;
endproperty : fifo_not_full_check

property fifo_full_check;
    @(posedge clk)
    count == MAX_ENTRIES |-> full;
endproperty : fifo_full_check

ERROR_reset_chk_fifo: assert property (de_assert_rst) else $error("");
ERROR_fifo_not_full_check: assert property (fifo_not_full_check) else $error("");
ERROR_fifo_full_check: assert property (fifo_full_check) else $error("");
```

Ex3: The same

Ex4:
```sv
property sig1_high_only_2_cycles_check;
    @(posedge clk)
    not (sig1 ##[1:2] sig1);
endproperty : sig1_high_only_2_cycles_check;
```
