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