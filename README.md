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

> `b[=3:5]` means `b` must be true for minimum 3 clocks and maximum 5 clocks but not necessarily consecutive

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







## Properties and Clocking

### Properties - Basics and types
- Defines behaviour of a design 
- Can be used for verification as an assumption, a checker or a coverage specification
  - Assert to specify the property as a checker to ensure that the property holds for the design
- Types of properties:
  - sequence
  - negation
  - disjunction
  - conjunction
  - if..else
  - implication
  - instantiation

**Sequence**
- Sequence evaluates to true iff there is a non-empty match of the sequence
- As soon as a match of `sequence_expr` is determined, the evaluation of the property is considered to be true

**Negation**
- `not property_expr` is used to negate the result of the evaluation of `property_expr`

**Disjunction**
- `property_expr1 OR property_expr2`
- The property evaluates to true iff at least one of the `property_expr` evaluates to true

**Conjunction**
- `property_expr1 AND property_expr2`
- The property evaluates to true iff both of the `property_expr` evaluates to true

**if..else**
- `if (expr) property_expr1`
- `if (expr) property_expr1 else property_expr2`

**Implication**
- Overlapping (evaluate the RHS in the same cycle)
  - `expr1 |-> expr2`
- Non-overlapping (evaluate the RHS in the next clock cycle)
  - `expr1 |=> expr2`

**Instantiation**
- An instance of a named property can be used as another `property_expr` or `property_spec`
```sv
property rule6(x,y);
    ##1 x |-> y;
endproperty

property rule5a;
    @(posedge clk)
    a ##1 (b || c) [->1] |->
        if (b)
            rule6(d,e);
        else // c
            f;
endproperty
```

### Recursive property
A named property is recursive if its declaration involves an instantiation of itself.

```sv
property prop_always(p);
    p and (1'b1 |=> prop_always(p));
endproperty
```


> Specifies that signal `p` must hold at every cycle. The `and` operator will return true if both operands return true 

```sv
assert property (@posedge clk) $fell(reset) |-> prop_always(bootStrap))
        else $error;
```

> The above ensure that after reset is de-asserted the signal `bootStrap` holds to 1. Anytime it goes low, the assertion fires.

For the `prop_always`, changing from non-overlapping implication to overlapping implication will results in an infinite loop recursion in the same cycle -> run-time error.

> Recursive call must always be evaluated (called) in the next cycle.

Example:

_Spec_: Interrupt must hold until interrupt `ack` is received.

Passing:
![](/note_img/passing_recursive_prop.png)

Failing:
![](/note_img/failing_recursive_prop.png)

```sv
property intr_hold(intr, intrAck);
    intrAck or (intr and (1'b1 |=> intr_hold(intr, intrAck)));
endproperty
```

> The `and` between intr and the recursive call will make sure that if `intr` goes low before `intrAck` -> the assertion fails
>
> The `or` make sure that the property pass when `intrAck` goes high

#### Restriction
- Operator `not` cannot be used in recursive property instances.
- Operator `disable iff` cannot be used in recursive property instances.
- If `p` is a recursive property, in the declaration of `p`, every instance of `p` must occur after a positive advance in time. (`|->` overlapping operator will cause runtime error - infinite loop).

#### Mutual recursion
Recursive properties can be mutally recursive
```sv
property chkPhase1;
    c |-> a and (1'b1 |=> chkPhase2);
endproperty
property chkPhase2;
    d |-> b and (1'b1 |=> chkPhase1);
endproperty
```
> This is valid since there is a time advancement (non-overlapping implication) and there is an antecedent

### Multiple clock sequences
- Multiple-clocked sequences are built by concatenating singly-clocked subsequences using the single-delay concatenation operator `##1`.
```sv
@(posedge clk0) sig0 ##1 @(posedge clk1) sig1
```
- A match of this sequence starts with a match of `sig0` at posedge `clk0`
- Then `##1` moves the time to the nearest strictly subsequent posedge `clk1`, and the match of the sequence ends at that point with a match of `sig1`

#### Restrictions
- Diffrently-clocked or multiply-clocked sequence operands cannot be combined with any sequence operators other than `##1`

> As we strictly look for next clocking event in the next clock after `##1` operator

- `and`, `or`, `intersect` are illegal in sequences with 2 clocks.

-> The `and`, `or`, `not` operators can be used in multiple-clock **properties** (not in sequences).

#### Multiple-clock properties

```sv
property mclk_prop;
    @(posedge clk1) b and @(posedge clk2) c; 
endproperty

assert property (@(posedge clk0) a |=> mclk_prop) else $error();
```

> The property `mclk_prop` means looks for the assertion of `b` signal each `clk1` posedge and the assertion of `c` signal each `clk2` posedge

![](/note_img/match_multiple_clock_prop.png)

A match happens if `b` and `c` are true and the next clock edge of `clk1` and `clk2` after `a` matches on an edge of `clk0`


*Using `not` operator in multiple clock property*

```sv
property mclk_prop;
    @(posedge clk1) b and @(posedge clk2) c; 
endproperty

assert property (@(posedge clk0) a |=> mclk_prop) else $error();
```

> Fails if `c` goes high on the `clk2` edge after `b` matches since we have a `not`


### Clock resolution 
- There are several ways to specify clock for a property
- Sequence instance has a clock
  ```sv
  sequence s2; @(posedge clk) a ##2 b; endsequence
  property p2; not s2; endproperty
  assert property (p2);
  ```

- Property itself has a clock
  ```sv
  property p3; @(posedge clk) not (a ##2 b); endproperty
  assert property (p3);
  ```

- Infer clock from the procedural block that calls the assertion
  ```sv
  always @(posedge clk) assert property (not (a ##2 b));
  ```

- Infer from the clocking block where property is declared
  ```sv
  clocking master_clk @(posedge clk);
      property p3;
          not (a ##2 b);
      endproperty
  endclocking

  assert property (master_clk.p3);
  ```

#### Clock resolution rules

Determined in decreasing order of priority:
- Explicitly specified clock for the assertion.
- Inferred clock from the context of the code when embedded.
- Default clock, if specified.

Clock needs to be explicitly specified for multi-clock assertions -> No default or inferred clock

Do not embed inside clocking blocks

### Binding assertions to design
Assertions can be either:
- Embeded in the design
- Defined outside the design (preferred)

> **Bind** is a way in which assertions defined outside the design can be bound to a design module or interface

Usage:
```sv
bind design_block_or_instance_name block_with_assertions
```

Binding possible to a specific instance or all instances of a module/interface

*Advantages:*
- Assertions can be added without changing the design files

Example: Interface `range` is instantiated inside a module `cr_unit` and hence every instance of module will have assertions:

```sv
interface range (input clk, enable, input int minval, expr);
    property crange_en;
        @(posedge clk) enable |-> (minval <= expr);
    endproperty
range_chk: assert property (crange_en);
endinterface

bind cr_unit range r1(c_clk, c_en, v_low, (in1&&in2));
```

### Expect
- `expect` statement is a procedural blocking statement that allows waiting on a property evaluation
- Same syntax as `assert` statement used inside a procedural block (though assert can be used outside procedural block also).

```sv
expect(property_spec) action_block
```

- `assert` is non-blocking while `expect` is blocking
  - `assert` always create a seperate thread and runs parallely
  - `expect` blocks the procedural block until the sequence/property completes
  
Example:
```sv
initial begin
    # 200ms;
    expect ( @(posedge clk) a ##1 b ## c ) else $error("expect failed");
    ABC: ...
end
```

> 200ms after the simulation start - if we see `a=1, b=1, c=1` in three consecutive cycles -> `expect` will pass
> 
> Since it is blocking, `ABC` will be execute 3 cycles after 200ms delay since the simulation start (if only the `expect` pass as there is a runtime error used in the `else` condition);
> 
- Useful for cases where certain sequences of events are expected and act based on that in the following procedural code

- Can also be used in tasks or class methods
- Can refer to both static and automatic variable since it's blocking code
```sv
integer data;
...
task automatic wait_for (integer value, output bit success);
    expect( @(posedge clk) ##[1:10] data == value ) success = 1;
    else success = 0;
endtask

initial begin
    bit ok;
    wait_for( 23, ok );
    ...
end
```

- `expect` doesn't infer clock from its preceding procedural block
-> Clock needs to be specified explicitly in the sequence or property it uses
```sv
sequence simple_seq;
    a ##1 b ##1 c;
endsequence

property simple_prop
    @(posedge clk) d |=> simple_seq;
endproperty

initial begin
    expect( @(posedge clk) simple_seq );
    expect simple_prop;
    @(posedge clk) expect (simple_seq);
end
```

> 1st and 2nd `expect` declaration is valid since clock is specified explicitly
> 
> 3rd declaration cause error since no clock specified.


## Tips and best usage
- Labelling: Always label meaningfully
  - Label gets printed during failure and also shows up in waveform
Example:
```sv
ERROR_q_did_not_follow_d:
    assert property ( @(posedge clk) disable iff (!rst_n) (q == $past(d)) );
```

- Static and dynamic casting:
  - Static cast: using the cast operator `'`
    - `int'(2.0 * 3.0)`
    - No return value on pass/fail condition possible
  - Dynamic cast: using the system task/function `$cast(dest, source)`
    - Can be called as a function (with return value) or a task (with no return value)
    - Return a pass/fail condition
    ```sv
    typedef enum{START, RUN, FINISH} States;
    States state;
    $cast(state, 2);
    ```
  > `$cast` will be useful with usage of base classes and derived classes in any advanced verification methodologies
  > 
  > Use an `assert()` around `$cast()` as a best practice to catch wrong casting
    ```sv
    typedef enum{START, RUN, FINISH} States;
    initial begin
        States state;
        int value;
        value = 3; // WILL FAIL IF CAST
        ERROR_bad_state: assert( $cast(state, value) );
    end
    ```

- Usage of macros
  ```sv
  `define assert_clk(arg, enable_error=0, msg="") \
      assert property ( @(posedge clk) disable iff (!rst_n) arg ) \
      else if(enable_error) $error("%t: %m: %s", $time, msg)
  ```
  - Usage:
  ```sv
  ERROR_q_did_not_follow_q: `assert_clk((q==$past(d)), 1, "***ERROR!!***");
  ```


## Functional Coverage Coding

### Introduction to Coverage
- Coverage is a metric of completeness of verification.
- Impossible to have directed testing for complex design -> Constrained random verification is used
  - Coverage is used to make sure what is getting verified
  - Make sure that all of importance design state space is verified
- 2 types: Functional and Code coverage

#### Code coverage
A way to analyze how many percentage of the source code have been covered during the simulation.
- Statement: has each statement of the source code been executed?
- Branch: Has each control structure been evaluated to both true and false? (if..else, while, repeat, forever, for...)
- Condition: has each boolean sub-expression evaluated both to true and false?
- Expression: Covers the RHS of an assignment statement
- Toggle: covers logic node transitions (cover 0->1, 1->0,)
- FMS: state coverage and FSM Arc coverage.

#### Functional coverage
Covers the functionality of the DUT. Functional coverage is derived from the specification.
- DUT inputs: Are all input operations injected?
- DUT outputs/functions: Are all responses seen from every output port?
- DUT internals: Are all interested design events being verified? (e.g. FIFO fulls, arbitration mechanisms)

Examples:
- Have I exercised all the protocol request types and combinations?
  - Burst reads, writes, atomic reads, flushes, etc.
- Have we accessed different memory aligments?
  - Byte aligned, word aligned, dword aligned
- Did we verify sequence of transactions?
  - Reads followed by writes
- Did we verify queue full and empty conditions?
  - Input and output Q getting full and new requests getting backpressured

> High code coverage + high functional coverage -> Good coverage

#### Coverage driven verification
```bash
From Verification Plan: -> Create initial coverage metrics
                                      ||
                                      \/
                              Generate Random Tests
                                      ||
                                      \/
                   ----------> Run Tests; Collect Coverage
                  ||                  ||
                  ||                  \/
                  ||                Coverage
                  ||                  goals   - Yes -> Verification complete
                  ||                  met?
                  ||                  ||
                  ||                  No
                  ||                  ||
                  ||                  \/
                  ||          Identify coverage holes
                  ||                  ||
                  ||                  \/
                  ||          Add tests to target holes
                  ---------- Enhance stimulus generator
                            Enhance coverage metrics if needed
```


### Covergroups and coverpoints - Basics
SV functional coverage constructs enable:
- Converage of variables and expressions, as well as cross coverage between them
- Automatic and also user-defined coverage bins
- Associate bins with sets of values, transitions or cross products 
- Events and sequences to automatically trigger coverage sampling
- Procedural activation and query of coverage

#### Covergroup
- Encapsulates the specification of a coverage model
- Is a user-defined type that allows collectively sampling process of all variables/transitions/cross that are sampled at the same clock (or sampling) edge
- Can be defined insde a package, module, interface, program block and class
- Once defined, can be instantiated using `new()` keyword

*Syntax*:
```sv
covergroup covergroup_name [([tf_port_list])] [coverage_event];
    { coverage_spec_or_option; }
endgroup[ : covergroup_name]
```

*Example*:
```sv
covergroup cg; 
    ... 
endgroup : cg

cg cg_inst = new;

```

#### Coverpoints
- A coverage point ("coverpoint") is a variable or an expression that functionally covers design parameters
- Each coverage point includes a set of bins associated with its sampled values or its value-transitions
- The bin can be automatically generated or manually specified
- A covergroup can contain one or more coverpoints

*Syntax*:
```sv
cover_point ::= 
    [ cover_point_identifier : ] coverpoint expression [ iff (expression) ] bins_or_empty

bins_or_empty ::= 
    { {attribute_instance} {bins_or_options;} }
    ;
```

*Example*:
```sv
covergroup g4;
    coverpoint s0 iff (!reset);
endgroup : g4
```

#### bin
- A `bin` is a construct used to collect coverage information
- Allows organizing coverpoint sample values in different ways
  - single value
  - values in range, multiple ranges
  - illegal values
- If the `bin` construct is not used, `coverpoint` will generate automatic values baased on the variable type
  - If variable is 2-bit -> 4 automatic bins are created

*Example*:
```sv
bins fixed[] = {1:10, 1, 5, 7} // 13 bins cre created
bins fixed[4] = {1:10, 1, 5, 7} // 4 bins are created with distribution <1,2,3>, <4,5,6>, <7,8,9>, <10,1,5,7>
```

```sv
bit [9:0] v_a;

coverpoint v_a {
  bins a = { [0:63], 65 };
  bins b[] = { [127:150], [148:191] };
  bins c[] = { 200,201,202 };
  bins d = { [1000:$] };
  bins others[] = default;
}
```

> a: single bin with either `65` or `[0:63]`
> 
> b: overlapping values in multiple bins
> 
> c: create 3 bins
> 
> d: $ = 1024 in this case (max value)
> 
> e: All other possible values

*Example 2:*
```sv
covergroup CovKind;
    coverpoint tr.kind {       // tr.kind is 4-bit wide
        bins zero = {0};       // A bin for kind == 0
        bins lo   = { [1:3] }; // 1 bin for values 1:3
        bins hi[] = { [8:$] }; // 8 seperate bins
        bins misc = default;   // 1 bin for all the rest 
    }
endgroup // CovKind
```

#### Covergroup arguments
- Generic/Parameterized covergroups can be writtern using arguments
  - Useful if similar covergroups are needed with different parameters or covering different signals
  - E.g. Covergroup for all basic FIFO conditions (for size, etc.)
- Actual values can be passed to formal arguments while covergroup is instantiated
- `ref` is needed if variable is passed as `actual` value to a formal argument. For const - `ref` is no need

*Example*: Same covergroup can be instantiate to cover attributes to two different address buses:

```sv
bit [16:0] rdAddr, wrAddr;

covergroup addr_cov (int low, int high, ref bit[16:0] address);
    @(posedge clk)
    addr_range_cp: coverpoint address {
      bins addr_bin = { [low:high] }
    }
endgroup : addr_cov

addr_cov rd_cov = new (0, 31, rdAddr);
addr_cov wr_cov = new (64, 127, wrAddr);
```

#### Covergroup inside class
- By embedding covergroup inside class - coverage can be collected on class members
- Very useful as it ia a nice way to mix constrained random stimulus generation along with coverage
- A class can have multiple covergroups
- Embedded covergroups must be instantiated (new-ed) inside the `new` (constructor) of the class

*Example:*
```sv
class xyz;
    bit [3:0] m_x;
    int m_y;
    bit m_z;

    covergroup cov1 @m_z;
        coverpoint m_x;
        coverpoint m_y;
    endgroup

    function new();
        cov1 = new;
    endfunction
endclass : xyz;
```

```sv
class MC;
    logic [3:0] m_x;
    local logic m_z;
    bit m_e;
    covergroup cv1 @(posedge clk); coverpoint m_x; endgroup
    covergroup cv1 @m_e; coverpoint m_z; endgroup
endclass
```

Passing arguments through the constructor (`new()` function of the class)
```sv
class C1;
    bit [7:0] x;

    covergroup cv (int arg) @(posedge clk);
        option.at_least = arg;
        coverpoint x;
    endgroup

    function new (int p1);
        cv = new (p1);
    endfunction 
endclass

initial begin
    C1 obj = new(4);
end
```

### Coverage bins
#### Bins for transition coverage
- Certain values or value ranges happening is considered.
- The existence of transition between two values or two value ranges is also considered.

*Specifiying transitions*
- Single value transition `value1 => value2`
- Sequence of transitions (sampled accross clock edged) `value1 => value3 => value4 => value5`
- A set of transitions (or range transition) `range_list1 => range_list2`
- Consecutive repetitions of transitions `trans_item [* repeat_range]`

*Example*
```sv
bit [4:1] v_a;

covergroup cg @(posedge clk);

    coverpoint v_a {
        // bins sa = (4 => 5 => 6), ( [7:9], 10 => 11, 12 );
        // the above is the same as the below
        bins sa = (4 => 5 => 6), ( ([7:9], 10) => (11, 12) );
        bins sb[] = (4 => 5 => 6), ( ([7:9], 10) => (11, 12) );
        bins allother = default sequence; 
    }

endgroup
```

- sa = `4=>5=>6`; `7=>11`; `8=>11`; `9=>11`; `10=>11`; `7=>12`; `8=>12`; `9=>12`; `10=>12`;
- sb will associate individual bins for all above transition

*Example #2*:
- Consecutive repetitions:
  ```sv
      // Consecutive repetitions of transitions
      bins <name> = { 3 [*5] }; // 3=>3=>3=>3=>3
      // Consecutive range of repetition:
      bins <name> = { 3 [*3:5] } // 3=>3=>3, 3=>3=>3=>3, 3=>3=>3=>3=>3
  ```
- Non-consecutive repetitions:
  ```sv
      // Consecutive repetitions of transitions
      bins <name> = { 3 [=> 3] }; // 3=>...=>3...=>3
  ```

#### Automatic bin creation
- SV creates implicit bins, when the coverage point does not explicitly specifies, it use the bins construct
- The size of automatic bin creation is decided by the cardinality of coverage point as long
  - For an enum coverage point, N is the cardinality of the enumeration
  - For any other integral coverage point, N is the minimum of 2M and the value of the `auto_bin_max` option, where M is the number of bits needed to represent the coverage point
- If the `auto_bin_max` option is less than the cardinality of the coverage point, the values are equally distributed among the bins
- Bins created automatically only consider 2-state values (not looking for the value `x` or `z`)
- Each auto bin will have a name of the form: `auto[value]`
  - Value -> single or range coverpoint value
  - Value -> enum constant on enum

*Example*
```sv
bit [2:0] rdAddr;

covergroup addr_cov @(posedge clk)
    coverpoint rdAddr;
endgroup
```

> In this example, the cardinality of coverpoint is 2^3 = 8 bins
> 
> If `auto_bin_max` is not specified - creates 8 automatic bins to cover each value
> 
> If `auto_bin_max` is 3, the values are distributed uniformly as `<0:1>, <2:3>, <4:5:6:7>` into 3 bins


#### Wildcard bin
- Wildcard bin is where all `x`, `z` or `?` will be treated as wildcards for `0` and `1`
  ```sv
  bit [2:0] port;
  covergroup CoverPort;
      coverpoint port {
        wildcard bins even = { 3'b??0 };
        wildcard bins odd = { 3'b??1 };
      }
  endgroup : CoverPort
  ```

*Example*
```sv
wildcard bins g12_16 = { 4'b11?? }; 
```

> The count of bin `g12_16` is incremeneted when the sampled variable is between 12 and 16: 1100 1101 1110 1111

```sv
// The count of transition bin T0_3 is incremented for
// the transitions: 00 => 10, 00 => 11, 01 => 10, 01 => 11
// as if by (0,1 => 2,3)

wildcard bins T0_3 = (2'b0x => 2'b1x);
```

#### Excluding bins
- Sometimes not all the bins will be interested or maybe some of them may not be valid to be covered
- 2 ways to exclude bins and also to put explicit checks
  - `ignore_bins`
  - `illegal_bins`

*`ignore_bins`*
- A set of values or transitions associated with a coverage-point can be explicitly excluded from coverage by specifying them as `ignore_bins`
  ```sv
  covergroup cg23;
      coverpoint a {
        ignore_bins ignore_vals = { 7,8 };
        ignore_bins ignore_trans = (1=>3=>5);
      }
  endgroup
  ```
> All values or transitions associated with ignored bins are excluded from coverage.
>
> Ignored values or transitions are excluded even if they are also included in another bin.


*`illegal_bins`*
- A set of values or transitions associated with a coverage-point can be marked as illegal by specifying them as `illegal_bins`
  ```sv
  covergroup cg3;
      coverpoint b {
        illegal_bins bad_vals = { 1,2,3 };
        illegal_bins bad_trans = (4=>5=>6);
      }
  endgroup
  ```

> These values are excluded from the coverage.
> 
> If they occur, a run-time error will be issued
> 
> They will result a run-time error even if they are also included in another bin.

*Example:* Create auto bins for 3 bit signal - but limit the coverage to only values 0 to 5 (instead of default 8 values)

```sv
bit [0:2] low_ports_0_5;

covergroup CoverPort;
    coverpoint low_ports_0_5 {
      ignore_bins hi = { 6,7 };
    }
endgroup : CoverPort
```

### Cross Coverage
- Coverage points measures occurrences of individual values
- Cross coverage measures occurrences of combination of values
- This is interesting because design complexity is in combination of events and that is what we need to make sure it is exercised as well 
  - Did I inject all combination of request types while my design's FSM is in all states?
- Cross coverage is specified between two or more coverpoints in a covergroup
- A cross of `N` coverpoints can be defined as the coverage of all combinations of all the bins associated with all of the `N` coverpoints
- For E.g. A cross of 2 coverpoints of 2 4-bit signals wil cover 256 combinations as each individual coverpoint will cover 16 combinations
  ```sv
  bit [3:0] a,b;

  covergroup cov @(posedge clk);
      aXb : cross a, b;
  endgroup
  ```
- Cross coverage is allowed only between coverage points defined within the same coverage group
- Cross coverage between expressions previously defined as coverage points is also allowed
  ```sv
  bit [3:0] a,b,c;

  covergroup cov2 @(posedge clk);
      BC: coverpoint b+c;
      aXb : cross a, BC;
  endgroup
  ```

*Example:*
```sv
bit [31:0] a_var;
bit [3:0] b_var;

covergroup cov3 @(posedge clk);
    A: coverpoint a_var { bins yy[] = { [0:9] }; }
    CC: cross b_var, A;
endgroup 
```

```
A: 10 bins
b_var: 16 bins
=> CC: 10 * 16 bins = 160 bins
```

#### Cross coverage bins select expression
2 expressions on bins:
- `binsof`
- `intersect`

*`binsof`*:
- Yields the bins of its expression in arguments `binsof(X)`
- The resulting bins can be further selected by including (or excluding) only the bins whose associated values intersect a desired set of values
- `binsof(x) intersect { y }`
  - Denotes the bins of coverage point `x` whose values intersect the range `y` given
- `!binsof(x) intersect { y }`
  - Denotes the bins of coverage point `x` whose values does not intersect the range `y` given
- Bins selection can be combined with `&&` and `||`

*Example:*
```sv
covergoup cg @(posedge clk);

    a: coverpoint v_a {
      bins a1 = { [0:63] };
      bins a2 = { [64:127] };
      bins a3 = { [128:191] };
      bins a4 = { [192:255] };
    }

    b: coverpoint v_b {
      bins b1 = { 0 };
      bins b2 = { [1:84] };
      bins b3 = { [85:169] };
      bins b4 = { [170:255] };
    }

    c : cross v_a, v_b {
      bins c1 = !binsof(a) intersect { [100:200] }; // 4 cross products
      // Only a1 is used for the cross since its not intersecting with [100:200]
      // a1 b1, a1 b2, a1 b3, a1 b4
      bins c2 = binsof(a.a2) || binsof(b.b2); // 7 cross products
      // Use a2 and b2 for cross products
      // a2 b1, a2 b2, a2 b3, a2 b4, b2 a1, b2 a3, b2 a4
      bins c3 = binsof(a.a1) && binsof(b.b4); // 1 cross product
      // Use both a1 and b4 only for cross product
      // a1 b4
    }
endgroup
```

#### Excluding cross products
- A group of bins can be excluded from coverage by specifying a select expression using `ignore_bins`
  ```sv
  covergroup yy;
      cross a,b {
        ignore_bins foo = binsof(a) intersect {5, [1:3]}; 
      }
  endgroup
  ```
- All cross products that satisfy the select expression are excluded from coverage
- Ignored cross products are excluded even if they are included in other cross-coverage bins of the enclosing cross

#### Specifying illegal cross products
- A group of bins can be marked as illegal from coverage by specifying a select expression using `illegal_bins`
  ```sv
  covergroup zz(int bad);
      cross x,y {
        ignore_bins foo = binsof(a) intersect {bad}; 
      }
  endgroup
  ```

### Coverage options
- Options control the behaviour of the `covergroup`, `coverpoint` and `cross`
- 2 types of options:
  - Specific to an instance of a covergroup
  - Specify for the covergroup
- Options placed in the cover group will apply to all cover points
- Options can also be put inside a single cover point for finer control

#### `option.comment`
Add a comment to make coverage reports easier to read
```sv
covergroup CoverPort;
    option.comment = "Section 3.2.14 Port numbers";
    coverpoint port;
endgroup
```

#### Per-instance coverage
- If the testbench instantiates a coverage group multiple times, by default SV groups togeter all the coverage data from all instances
- Sometime coverpoints are hit on all instances of the covergorup but not cumulatively
-> Use the `option.per_instance = 1`

```sv
covergroup CoverLength;
    coverpoint tr.length;
    option.per_instance = 1;
endgroup
```

#### Coverage threshold using `option.at_least`
- By default a coverpoint is marked as 100% hit if it is hit at least once.
- Sometime the threshold needed to be changed (bigger)
- Usage: `option.at_least = 10`
  
#### Coverage goal option
- By default a covergroup or a coverpoint is considered fully covered only if it hit 100% of coverpoints or bins
- The can be changed using `option.goal` if a less goal is wanted to settle.

#### `option.weight`
- If set at the covergroup level, it specifies the weight of this covergroup instance for computing the overall instance coverage
- If set at the coverpoint (or cross) level, it specifies the weight of a coverpoint (or cross) for computing the instance coverage of the enclosing covergroup
- Usage: `option.weight = 2` (default is 1) 
- Useful when prioritizing certain coverpoints/covergroups as "must" hit versus less important

*Example*
```sv
covergroup cross_weight;
    a: coverpoint siga {
      bins a0 = {0};
      option.weight = 0; // Will not be used in computing coverage
    }
    b: coverpoint sigb {
      bins b1 = {1};
      option.weight = 1;
    }
    ab: cross a,b {
      option.weight = 3;
    }
endgroup
```

> Individual coverage on signal is of no interest - but only useful in cross coverage

#### `auto_bin_max` and `cross_auto_bin_max`
Use to specified maximum number of bins for coverpoints and crosses


### Coverage methods, performance, coverage properties and misc

#### Predefined coverage methods
![](/note_img/predefined_coverage_function.png)

- `void sample()`
  - Useful when coverage sampling needs to be done based on some event or condition and not always
  - Example: For an 2x2 switch - coverage for all packet fields needs to be measured only on events when packet is received
  ```sv
  covergroup packet_cov_cg;
      coverpoint dest_addr;
      coverpoint packet_type;
  endgroup

  packet_cov_cg pkt_cov;
  pkt_cov = new();

  always @(pkt_recieved) begin
      pkt_cov.sample();
  end
  ```

- `void start()` and `void stop()`
  - Useful when you want to start/stop sampling on certain conditions
  - Example: If a port is disabled dynamically - stop coverage sampling until it is enabled again
  ```sv
  covergroup packet_cov_cg @(posedge clk)
      coverpoint dest_addr;
      coverpoint packet_type;
  endgroup

  packet_cov_cg pkt_cov;
  pkt_cov = new();

  always @(posedge clk) begin
      if (port_disable)
          pkt_cov.stop();
      else if (port_enable)
          pkt_cov.start();  
  end
  ```

*Predefined tasks and functions*: Help managing coverage data collection

- `$set_coverage_db_name(name)`
  - Sets the filename of the coverage database into which coverage information is saved at the end of a simulation run
- `$load_coverage_db(name)`
  - Load from the given filename the cumulative coverage information for all coverage group types 
- `$get_coverage()`
  - Returns as a real number in the range 0-100 the overall coverage of all coverage group types

#### `cover property`
- Use the same SVA temporal syntax and define sequences and properties
- The same property that is used as an assertion can be used for coverage using `cover property` keyword
- Syntax: `cover property (sequence_expr) statement_or_null`

```sv
property abc;
    @(posedge clk) !a |-> b ##1 c;
endproperty

cp_abc: cover property (abc) $display("Coverage abc seq passed");
```
- The rsult of coverage statement for a property shall contain:
  - Number of times attempted
  - Number of times succeeded
  - Number of times failed
- The `statement_or_null` is executed everytime a property succeeds

#### Performance implications
- Enabling Functional coverage slows down the simulation
- It is important to know what should be covered and what should not:
  - Don't cover all values for big buses. E.g.: It might only be interesting to cover select address ranges for a 32-bit address bus
  - Same applies for counter ranges, FIFO/Data structure depth, etc.
  - Don't use auto bins for such wide variables. Be careful while using autobins and cross as it can explode the coverage bins. It's also hard to debug as names are also auto generated
  - Use `cross` and `intersect` to weed out unwanted bins
- Should know when to enable/disable sample a covergroup:
  - Disable coverpoint/covergroup during reset
  - Don't blindly use clock events to sample coverpoint variables -> Use selective `sample()` methods
  - Use `start()` and `stop()` methods to decide when to start/stop evaluating coverage
  - Do not duplicate coverage across covergroups and properties
  
#### Collecting and analyzing coverage
- Mostly controlled by simulation tools
- Coverage database, merging, report generation and viewers are all supported by different tools
