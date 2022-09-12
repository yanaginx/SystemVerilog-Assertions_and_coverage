# SystemVerilog Assertions and Coverage Coding

## SystemVerilog Assertions - Basics and sequences

---

### Introduction to Assertions

#### What is assertions

Assertion is a check against a design specification or rule

> A way to capture a certain specification or rule and then use that as a check in the simulation phase

→ To make sure that the rule is never violated by the design

Example for assertions:
![](/note_img/assertion_example.png)

#### Why assertions

- Checking the intent of the design
- Improves **observability** and **debug ability**
  - Effect of an internal bug can be observed at line of code instead of propagating into outputs
  - Eg: An illegal state transition in a FSM
    > Failure can be found right at the line of code where assertions failed
  - Eg: An illegal combination of certain signal values
- Checking if design specification was covered in verification process
  - Eg: Design has a specification to back pressure a request when a FIFO is near full
  - Assertion can make sure this rule is not violated
    " A coverage on this property makes sure that the scenario is verified
- Readable hence can be served as design documentation
- Same assertions can be used in _Formal Verification_ where algorithms can exhaustively check for violations
- Can be parameterised and re-used across designs
- Can be turned on/off selectively
- A subset of assertions can be synthesized and used in emulations

**Assertion Based Verification (ABV) Methodology** -> defines how Assertions are used

#### Assertion Coverage

- Tools can report out Assertions coverage
  - Number of assertions that are never hit
  - Multiple branches in an Assertion-covered
- Help to see if Verification plan captures all assertions needed

### SystemVerilog Assertion (SVA)

- Two common types of Assertions
  - Immediate Assertions
  - Concurrent Assertions

#### Immediate assertions

Assertions that test a condition at the current time

- Non-temporal (not depending on time) -> Checks that are done on any given condition at any given time
- Executed like procedural statements (if..else..)
- Assertions fails if expression evaluate to X,Z,0
- Can be used in `initial`/`always` blocks and `tasks`/`functions`

```sv
[name:] assert (expression) [pass_statement] [else fail_statement]
```

Example:

> Assertions fails if `state=REQ` without `req1` or `req2` enabled (being 1)

```sv
time t;
always @(posedge clk)
    if (state == REQ)
        assert (req1 || req2)
        else begin
            t = $time;
            #5 $error("Assert failed at time %0t", t);
        end
```

More example:

> Assertions' failure will emit the `event1`

```sv
assert (myfunc(a,b))
    count1 = count + 1;
else ->event1;
```

> Assertion used to check if y != 0 in any given time

```sv
assert (y == 0)
else flag = 1;
```

> Assertion used to check if the state is not $onehot

```sv
always @(state) begin
    assert (state == $onehot)
    else $fatal;
end
```

#### Severity/Error handling

- Assertion failure is associated with a severity:
  - `$fatal` is a run-time fatal
  - `$error` is a run-time error
  - `$warning` is a run-time warning, can be suppressed in a tool-specific manner
  - `$info` indicates that the assertion failures carries no specific severity

> Specify how severe a assertion will fail

#### Concurrent assertions

Assertions that test for a sequence of events that spread over multiple clock cycles

- Temporal
- `property` keyword used to distinguishes a concurrent assertion from an immediate assertion
- Concurrent because they execute in parallel with other design blocks

```sv
[name:] assert property (cont_prop(rst,in1,in2)) [pass_stat] [else fail_stat];
```

Assertions is evaluated only at the occurence of a clock ticks

> The values of variables used are sampled values. Values are sampled in simulation ticks

![](/note_img/value_sampling_on_simulation.png)

#### Concurrent Assertions Evaluation

Concurrent Assertions expression are:

- Sampled in a preponed region
- Evaluated in an observe region, using sampled value
- Execute pass/fail statements in re-active region

SystemVerilog value evaluation in a timeslot:
![](/note_img/value_sampling_details.png)

#### Basic Example

Request-Grant protocol Spec: **Request** high should be followed by **Grant** after 2 cycles, then **Request** is deactivated along with **Grant**.

```sv
property req_grant_prop
    @(posedge clk) req ##2 gnt ##1 !req ## !gnt;
endproperty

assert property req_grant_prop else $error("Req-Gnt Protocol Violation");
```

> `##2` means the time consuming of 2 cycles
>
> `##` means the another cycle later

#### Case Study:

- Design spec: Simple Round Robin Arbiter with 3 input requests `req1`, `req2`, `req3` and output `grant1`, `grant2`, `grant3`

- Immediate

  - After reset - None of `req1`/`req2`/`req3` can be X/Z
  - `grant1`, `grant2` and `grant3` cannot be High at the same cycle

- Concurrent
  - `req1`/`req2`/`req3` going high should be followed by `grant1`/`grant2`/`grant3` in "n" cycles

### Assertions, Properties, Sequences

- Assertion can include a property directly
- Assertion can be split into assertion and a property declaration

```sv
assert property (my_prop);
property my_prop;
  @(posedge clk)
    disable iff (!reset)
    a |=> b ##1 c;
endproperty
```

The above can be written as

```sv
assert property (@(posedge clk) disable iff (!reset) a |=> b ##1 c);
```

Assert property can be disable under certain condition -> use `disable` for conditional disable

- Property block contains definition of sequece of events
- Complex properties can be structured using multiple sequence blocks

Example for a sequence block:

```sv
sequence s1;
    @ (posedge clk) a ##1 b ##1 c;
endsequence
```

> Whenever the condition is true: `a` high followed by `b` high after one cycle followed by `c` high after another cycle then it is called a sequence match

```sv
sequence s2;
    @ (posedge clk) a ##1 c;
endsequence
```

Using those 2 sequences in the property:

```sv
property p1;
    @(posedge clk) disable iff (!reset)
    s1 |=> s2;
endproperty
```

> If sequence 1 (`s1`) occurs then sequence 2 (`s2`) should also occurs

#### Sequences

- A sequence is a series of true/false expressions spread over one or more clock cycles
- Acts as basic building blocks to create complex property specifications
- Sequences are built over SystemVerilog boolean expressions

Example:

```sv
sequence s1;
    @(posedge clk) a ##1 b ##1 c;
endsequence
```

```sv
sequence t2;
    (a ##[2:3] b) or (c ##[1:2] d);
endsequence
```

> When `a` is asserted, `b` should be asserted after 2 or 3 cycles OR when `c` is asserted, `d` should be asserted after 1 or 2 cycles

- **Linear sequence** is a finite list of SystemVerilog boolean expressions in a linear order of increasing time
- A sequence is said to matched if:
  - The first boolean expression evaluates to true at the first clock tick
  - The second boolean expression evaluates to true after the delay from first expression
  - And so forth, up to and including the last boolean expression to true at the last clock tick

```sv
sequence s1;
    @(posedge clk) a ##1 b ##1 c;
endsequence
```

> In this example, there are 3 boolean expressions. At any given clock tick when `a` is set to true (first boolean expression), after 1 clock cycle (##1) `b` (second boolean expression) has to be true and so on.

- Sequence can be declared in:
  - Module
  - Interface
  - Program
  - Clocking block
  - Package

```sv
sequence sequence_identifier[([list_of_formals])];
  { assertion_variable_declaration }
  sequence_expr;
endsequence [:sequence_identifier]
```

- Sequences can have option formal arguments:
  - Actual arguments can be passed during instantiation
  ```sv
  sequence s20_1(data, en);
    (!frame && (data==data_bus)) ##1 (c_be[0:3] == en);
  endsequence
  ```
  > clock don't always have to be specified. In this case clock will be inferred from the property or assert where this sequence is instantiated

#### Implication operator

- Evaluation of a sequence can be pre-conditioned with an implication operator
  - Antecedent - LHS of implication operator
  - Consequence - RHS of implication operator
- Implication is a way to specify:
  - If Antecedent matches then consequence will execute

```sv
property p1;
    @(posedge clk) disable iff (!reset)
    start |-> request ##2 (grant==1 && req==0);
endproperty
```

> In the example, if start asserted then the sequence in the RHS will also happen

- Two types of implication operator:
  - Overlapped (`|->`):
    - If precondition (LHS) is true - RHS sequence evaluation start immediately (in the **same** clock cycle)
    - If precondition (LHS) is false - RHS sequence acts as if succeeded (no evaluation occurs)
      ![](/note_img/overlapped_implication.png)
  - Non-overlapped (`|=>`)
    - If precondition (LHS) is true - RHS sequence evaluation start in the **next** clock cycle
    - If precondition (LHS) is false - RHS sequence acts as if succeeded (no evaluation occurs)
      ![](/note_img/nonoverlapped_implication.png)

#### Cycle delays operator

- `##` represents cycle delay (or number of sampling edges)

- `##n` specifies `n` clock cycles

  > `##0` means same cycle - overlapping signals

- `##[min:max]` specifies a range of clock cycles

  - `min` and `max` must be zero or greater
  - Sequence will match on the very first intance of n in the window of `min` to `max` cycles

- `$` specifies infinite number of cycles (til simulation ends)

  > `req ##[1:$] grant`

  Meaning asserting `req` signal will eventually followed by asserting `grant` signal without specifying how long after the assertion of `req`

#### Repetition operator

- Sequence of events can be repeated for a repeated count using `[*n]`
  - `n` must be >= 0
  - `n` cannot be equal to `$`

```sv
sequence a_b
    @(posedge clk) a ##1 b[*2];
endsequence
```

> `b[*2]` means `b` must be true for 2 consecutive clocks

_Usage_: If parity error detected - error log should be high for `n` number of clocks

- Consecutive repetition can occurs for a range count using `[*m:n]`

```sv
sequence a_b
    @(posedge clk) a ##1 b[*2:5];
endsequence
```

> `b[*2:5]` means `b` must be true for minimum 2 consecutive clocks and maximum 5 consecutive clocks

The sequence is equivalent to:

```sv
a ##1 b ##1 b ||
a ##1 b ##1 b ##1 b ||
a ##1 b ##1 b ##1 b ##1 b ||
a ##1 b ##1 b ##1 b ##1 b ##1 b
```

- `[=m]` operator can be used if an event repetition of `m` non-consecutive cycles are to be detected
  - `m` must be >= 0
  - `m` cannot be equal to `$`

```sv
sequence a_b
    @(posedge clk) a ##1 b[=3];
endsequence
```

> `b[=3]` means `b` must be true for 3 clock cycles but not necessarily consecutive

_Usage_: if a burst read of length = 4 request happens - if we want to check that 4 read `data` and `ack` - not necessarily in consecutive cycles

- Non-consecutive repetition can occurs for a range count using `[=m:n]`

```sv
sequence a_b
    @(posedge clk) a ##1 b[=3:5];
endsequence
```

> `b[=3:5]` means `b` must be true for minimum 3 clocks and maximum 5 clocks but not necessarily

- Empty sequence: a sequence that does not match over any positive number of clocks
  > `a[*0]`

Example #1:

```sv
a ##2 b ##1 a ##2 b ##1 a ##2 b ##1 a ##2 b ##1 a ##2 b
```

Can be simplified to:

```sv
(a ##2 b)[*5]
```

Example #2:

```sv
a[*0:3] ##1 b ##1 c
```

is equivalent to

```sv
b ##1 c ||
a ##1 b ##1 c ||
a ##1 a ##1 b ##1 c ||
a ##1 a ##1 a ##1 b##1 c
```

#### AND operator

- Use `AND` operator if two sequence operands need to match

  > `Seq1 AND Seq2`

- The resulting sequences matches if:

  - Both `Seq1` and `Seq2` matches when starting from the same start point
  - Resulting sequence match is at the cycle when both matches
  - The end time for individual sequences can be different. The end time of the resulting sequence will be the end time of the longest one

- If both operands are sampled signals instead of sequences
  -> Both needs to be evaluate to true at the same cycle for the `AND` to match

Example #1:
![](/note_img/AND_operator_example.png)

In the example the resulting sequence from the `AND` operator match at the match of the later sequence (`te3 ##2 te4 ##2 te5`)

> Both sequences must have the same evaluating point

In the example, same evaluating point can be: clk cycle 2 and clk cycle 8

Example #2:
![](/note_img/AND_operator_example_2.png)

In this example, there are 2 matchs possible because either the first or the second operand (sequence) can end first

Example #3:
![](/note_img/AND_operator_example_3.png)

#### Intersection operator (`intersect`)

- Same as `AND` operator - except that the length (the time period) of operands has to match
  > Meaning the end time of both sequences must match

Example:

```sv
(te1 ##[1:5] te2) intersect (te3 ##2 te4 ##2 te5)
```

![](/note_img/intersect_operator_eaxmple.png)

In this example, only 1 match possible at cycle 12 since the end cycle of both sequences must match.

#### OR operator

- The operator `OR` is used when at least one of the two operand sequences is expected to match

  > `Seq1 OR Seq2`

- The resulting sequences matches if:

  - Both `Seq1` and `Seq2` matches when starting from the same start point
  - Resulting sequence matches when either `Seq1` or `Seq2` match
  - The end time for individual sequences can be different. The end time of the resulting sequence will be the end time of the latest matched one

- If both operands are sampled signals instead of sequences
  -> Match happends when one of them evaluate to true

Example #1:
![](/note_img/OR_operator_example.png)

Example #2:
![](/note_img/OR_operator_example_2.png)

Example #3:
![](/note_img/OR_operator_example_3.png)

#### Case study: Application of `AND`/`OR`

Spec: If write burst length == 4, write lengths can be 1, 2 or 4

```sv
property BurstLengthValid
    @(posedge clk) disable iff (!rst)
    ((burstLen == 4) |-> (wrlen==1) OR (wrlen==2) OR (wrlen==4));
endproperty

assert property (BurstLengthValid)
```

#### `first_match` operator

The `first_match` operator matches only the first of multiple possible matches for an evaluation attempt of its operand sequence.

The remaining mathces are discarded

```sv
sequence t1;
    te1 ##[2:5] te2;
endsequence
```

The sequence can have multiple matches:

```sv
te1 ##2 te2
te1 ##3 te2
te1 ##4 te2
te1 ##5 te2
```

Example #1

```sv
sequence t2;
    (a ##[2:3] b) OR (c ##[1:2] d);
endsequence

sequence ts2;
    first_match(t2);
endsequence
```

Possible matches for `t2`:

```sv
a ##2 b
a ##3 b
c ##1 d
c ##2 d
```

Possible matches for `ts2` are only the first of the 4 matches above

#### Case study: `first_match` usage

_Spec_: Every time a PCI bus goes idle, state machine should go back to IDLE state

> A PCI BUS Idle can be detected if `frame` and `irdy` signal are high for at least 2 cycles

```sv
sequence checkBusIdle
    (##[2:$] (frame && irdy));
endsequence

property first_match_idle
    @(posedge clk) first_match(checkBusIdle) |-> (state==busidle);
endproperty
```

#### `throughout` operator

- Useful for testing a condition like a "signal" or an "expression" is true throughout a sequence
- Usage: `sig1/exp1 throughout seq1`
- LHS of `throughout cannot be other sequence

Example:

_Spec_: Once burst mode signal goes low and 2 cycles later `irdy`/`trdy` signal goes low for 7 consecutive cycles - the burst mode signal should remain low throughout

> Once `irdy`/`trdy` goes low for 7 consecutive cycles, burst_mode signal should never goes high

```sv
sequence burst_rule1;
    @(posedge mclk)
        $fell(burst_mode) ##0
        (!burst_mode) throughout (##2 ((trdy==0) && (irdy==0)) [*7]);
endsequence
```

> `$fell` is to keep track of the negedge of the signal (going from high to low)

> When `$fell` happens, in the same cycle, the `burst_mode` must be low throughout the deassertion of `trdy` and `irdy` for 7 consecutive cycles

![](/note_img/matching_throughout_sequence.png)

![](/note_img/failing_throughout_sequence.png)

#### `within` operator

- Useful for testing a condition where a sequence is overlapping in part length of another sequence
- Usage: `seq1 within seq2`
- `seq1 within seq2` matches if `seq2` matches along the interval and `seq1` matches along some sub-interval of consecutive clock ticks during the interval

Example:

_Spec_: `trdy` has to be low for 7 cycles 1 cycle after `irdy` goes low and `irdy` stays low for 8 cycles

```sv
!trdy[*7] within (($fell irdy) ##1 !irdy[*8])
```

![](/note_img/matching_within_sequence.png)

The above sequence match from clock 4(?) till clock 11

#### `not` operator

- Usage: `not(seq_exp)`
- Example:

_Spec_: After going high, the sequence of abc should not happen.

```sv
sequence seq_abc;
    a ##1 b ##1 c;
endsequence

property nomatch_seq;
    @(posedge clk) start |-> not(seq_abc);
endproperty

assert property nomatch_seq else $error();
```

Example #1:

_Spec_: Squence `cd` should never follow sequence `ab`

```sv
property no_cd_after_ab;
    not (a ##1 b |-> c ##1 d);
endproperty
```

> Though this looks right, the implication operator cause `c ##1 d` only be evaluated once `a ##1 b` matched. Since there is a not, this can cause false failures as property also matches when `a ##1 b` doesn't match.

```sv
property no_cd_after_ab;
    not (a ##1 b ##0 c ##1 d);
endproperty
```

> Using `##0` will make this works correctly

#### `if` in property

- It is possible to select multiple property expressions using `if..else` condition inside a property

```sv
if(exp) property_expression1 else property_expression2
```

- Used mostly in properties with `antecedent |-> consequent` type of assertions

- Based on antecedent - we use an `if..else` condition in the consequent expression

Example:

_Spec_: Signal `master_req` high should be followed by at least one of `req1` or `req2`. If `req1` then `ack1` should follow else `ack2`

```sv
property master_child_reqs;
    @(posedge clk) master_req ##1 (req1 || req2) |->
    if (req1)
        (##1 ack1)
    else
        (##1 ack2);
endproperty
```

_Spec_: on a cache access, if there is a cache lookup hit then `state=READ_CACHE` else if it's a miss `state=REQ_OUT`

```sv
property cache_hit_check
    @(posedge clk) (state == CACHE_LOOKUP) ##1 (CHit || CMiss) |->
    if (CHit)
        state == CACHE_READ;
    else
        state == REQ_OUT;
endproperty

assert property(cache_hit_check) else $error;
```

#### `ended` operator

- Used to detecting endpoint of sequence
- Usage: `<seq_instance>.ended`
- Returns true when the sequence has reached the end point at that point in time or else return false

```sv
sequence e1;
    @(posedge sysclk) $rose(ready) ##1 proc1 ##1 proc2;
endsequence

sequence rule;
    @(posedge sysclk) reset ##1 inst ##1 e1.ended ##1 branch_back;
endsequence
```

In the sequence `rule`, state that 1 cycle after `reset` going high, `inst` must be asserted and after `inst` assertion for 1 cycle, `e1` must be ended. After `e1`'s end for 1 cycle, `branch_back` must be asserted.

> Sequence `e1` must match (or end) exactly one cycle after `inst` assert

For this case when using sequence instance:

```sv
sequence rule;
    @(posedge sysclk) reset ##1 inst ##1 e1 ##1 branch_back;
endsequence
```

This means `e1` is required to start 1 cycle later after `inst` is asserted

Using `.ended` with non-overlapping implication:

![](/note_img/ended_with_non_overlap.png)

With the same example, for overlapping implication, the rose of `c` and the end of `ARbseq` must happen in the same cycle:
![](/note_img/ended_with_overlap.png)

#### Local variables

- Can be used in a sequence as well as in the properties
- Dynamically created when needed inside sequence instance and removed when sequence ends
- Each instance of sequence will have its own copy of the variable
- Local variables can be written on repeated sequences and accomplish accumulation of values

```sv
sequence rep_v;
    int x;
    `true, x=0 ##0
    (!a [*0:$] ##1 a, x=x+data)[*4] ##1 b ##1 c && (data_out == x);
endsequence
```

- The local variables declared in one sequence are not visible in the sequence where it gets instantiated:

```sv
sequence L_seq;
    int lv_data;
    (rdC, lv_data=rData);
endsequence;

sequence H_seq;
    c ##1 L_seq ##1 (wData == lv_data); // `lv_data` not visible inside H_seq
endsequence;
```

Example #1:

_Spec_: The `rdData` associated with `rdDone` signal for a cache read gets written to register after 3 cycles with an incremented value

```sv
sequence rd_cache_done;
    ##[1:5] rdDone;
endsequence;

sequence check_reg_wr_data;
    int local_data;
    (rd_cache_done, local_data=cache_rd_data) ##2 (reg_wr_data == (local_data+1))
endsequence
```

Example #2:

_Spec_: Once a read has been issued with a `readId`, another read cannot be issued with the same `readId` until `readAck` for the first `readId` comes back

```sv
property checkReadIdAck;
    int loc_id;
    ($rose(read), loc_id = readId) |=>
    not (($rose(read) && readId == loc_id) [*1:$]) ##0
    ($rose(readAck) && readAckID == loc_id)
endproperty;
```

> Save `readId` on first read then we continue to check for "no" read with the same `readId` (continue till $) until we have the `readAck` of the same `readAckID`

#### Subroutines

- Tasks, void functions and system functions/tasks can be called at the end of a **successful** match on sequence

```sv
sequence s1;
    logic v,w;
    (a,v = e) ##1
    (b[->1], w = f, $display("b after a with v = %h, w = %h\n", v, w);
endsequence;
```

> `s1` matches strictly on first occurence of `b` 1 cycle after occurence of `a`. On the match - system task `$display` is used to print the local variables

#### Sampled value functions

- Special system functions are available for accessing sampling values of an expression:

  - Access current sampled value
  - Access sampled value in the past
  - Detect changes in sampling values

- Can also be used in procedural code in addition to assertions

- `$rose`, `$fell`

  - `$rose(expression[, clocking_event])`
    - returns true if the least significat bit of expression changed to 1 from previous clocking event and otherwise returns false
    - Sampled value in previous clock can be - `0`, `x` or `z`.
  - `$fell(expression[, clocking_event])`
    - returns true if the least significat bit of expression changed to 0 from previous clocking event and otherwise returns false
    - Sampled value in previous clock can be - `1`, `x` or `z`.
  - Clocking event is optional and is usually derived from the clocking event of assertion or inferred clock for procedural block

  > `$rose` and `$fell` should only be used with 1-bit signal, if a vector is used -> only the lower bit will be looked at

  - `$rose(signal)` is different from `@(posedge (signal))`

    - `@(posedge (signal))` is true when signal changes from `0` to `1`
    - `$rose(signal)` is true when the change to `1` happens across 2 clocking events

  - Usage of `$fell`

  _Spec_: If `write_en` goes low (indicating write operation) then `write_data` should not be `x`

  ![](/note_img/fell_spec_example.png)

  ```sv
  property check_data_we;
      @(posedge clk) $fell(write_en) |-> not ($isunknown(wr_data));
  endproperty
  ```

- Why sampling is needed?

_Spec_: `ack` should be asserted 2 cycles after `req` is asserted
![](/note_img/correct_and_wrong_behaviour_example.png)

Correct:

```sv
property check_req_ack_correct;
@(posedge clk) req |=> ##2 $rose(ack);
endproperty
```

> Actual assertion (rising from 0 to 1) must be recorded

Wrong:

```sv
property check_req_ack_wrong;
@(posedge clk) req |=> ##2 ack;
endproperty
```

- `$stable`

  - Usage: `$stable(expression [, clocking_event])`
  - Returns true if value of expression did not change from its sample value at previous clock and otherwise returns false
  - Example: Register data should be stable when `rd_en` goes high

  ```sv
  property reg_rd_data_stable;
      @(posedge clk) rd_en |-> $stable(reg_data);
  endproperty
  ```

- Example usage in procedural block and continuous assignment:

  - Procedural block

  ```sv
  always @(posedge clk)
      TestDone <= stimulus_over & $rose(unit_done);
  ```

  ```sv
  always @(posedge clk) begin
      if ($stable(my_sig)) begin
          $display($time, "my_sig is stable from previous clk");
      end
  end
  ```

  - Continuous Assignment

  ```sv
  assign intr_cleared = $fell(intr, @(posedge clk));
  assign set = $rose(intr, @(posedge clk));
  ```

- `$pass`

  - An assertion can use the sampled value of an expression prior to any number of clock cycles in the past

  - `$pass (expr [, num_cycles] [, gating_expr] [, clock_event])`

    - `num_cycles` defaults to 1 if not specified
    - `gating_expr` - optional gating expression for clocking event
    - `clock_event` - if not specified will infer from property/assertion

  - Example:

  _Spec_: If `ack` is true then there was a request asserted 2 cycles before

  ```sv
  property ReqCausedAck;
      @(posedge clk) $rose(ack) |-> $past(req, 2);
  endproperty
  ```

- More Examples:

_Spec_: if current state is `CACHE_READ`, then previous state cannot be `CACHE_MISS`

```sv
property cache_read_chk;
    @(posedge clk) (state == CACHE_READ) |-> ($past(state) != CACHE_MISS);
endproperty
```

#### System functions and Tasks

- Useful in creating assertions/sequences/properties
  - `$onehot`
  - `$isunknown`
  - `$countones`

- Can be used in assertions as well as in normal procedural blocks

- `$onehot`
  - Usage: `$onehot (expression)`
  - Returns true if there is only one bit of the expression is high
  - `$onehot` will fail if expression is `z` or `x`
  - Example: For an arbiter with `n` requests there can be only one grant at any cycle along with `ack`
    ```sv
    property arb_gnt_chk;
        @(posedge clk) disable iff (reset) arb_ack |-> $onehot(arb_gnt_bus);
    endproperty
    ```

- `$onehot0`
  - Usage: `$onehot0 (expression)`
  - Returns true if at most one bit of the expression is high (if all bits are zeros or if at most one bit is 1)
  - `$onehot` will fail if expression is `z` or `x`
  
- `$isunknown`
  - Usage: `$isunknown (expression)`
  - Returns true if any bit of expression is `z` or `x` (equivalent to `^(expression) === 'bX`)
  - Example: If a request is valid - then the request `address` and `data` and `id` signals should not be `X`
    ```sv
    property req_attr_check_X;
        @(posedge clk) disable iff (reset) reqValid |-> not ($isunknown( {reqAddr, reqData, reqId} ));
    endproperty
    ```

- `$countones`
  - Usage: `$countones (expression)`
  - Returns true if there is only one bit of the expression is high
  - `$countones` will not count if any bits is `z` or `x`
  - Example: For an arbiter with `n` requests there can be only one grant at any cycle along with `ack`
    ```sv
    property arb_gnt_chk;
        @(posedge clk) disable iff (reset) arb_ack |-> ($countones(arb_gnt_bus) == 1);
    endproperty
    ```

- `$assertoff`, `$asserton`, `$assertkill`
  - `disable iff` gives a local control in the source of assertion
  - `$assertoff`, `$asserton`, `$assertkill` gives a global control on assertions at module or instance level
  - `$asserton` is default: can also be called after `$assertoff` or `$assertkill` to restart turning on of assertions
  - `$assertoff` - temporarily turns off execution of assertions
  - `$assertkill` - kills all currently executing assertions
  - Usage:
    ```sv
    $assertoff (level, [list_of_module, _instance or assertion_identifier])
    $asserton (level, [list_of_module, _instance or assertion_identifier])
    $assertkill (level, [list_of_module, _instance or assertion_identifier])
    ```
    - Level 0: turns on/off assertions at ALL levels below current module/instance
    - Level n: turns on/off assertions at n levels of hierachy below current module/instance
    - `assertion_identifier` - name of property or label used with assert
  - Example: Disable all asserts during reset and enable after reset de-assertion:
    ```sv
    module assert_control();
        initial begin: disable_assert_during_reset
            @(negedge top_tb.reset_n) // active low reset
                $display("Disabling assertion during reset");
                $assertoff(0, top_tb.cpu_inst1);
            @(posedge top_tb.reset_n)
                $display("Enabling assertions after reset");
                $asserton(0, top_tb.cpu_inst1);
        end
    endmodule
    ```
