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

> `##2 means the time consuming of 2 cycles `## means the another cycle later

#### Case Study:

- Design spec: Simple Round Robin Arbiter with 3 input requests `req1`, `req2`, `req3` and output `grant1`, `grant2`, `grant3`

- Immediate

  - After reset - None of `req1`/`req2`/`req3` can be X/Z
  - `grant1`, `grant2` and `grant3` cannot be High at the same cycle

- Concurrent
  - `req1`/`req2`/`req3` going high should be followed by `grant1`/`grant2`/`grant3` in "n" cycles
