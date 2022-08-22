# SystemVerilog Assertions and Coverage Coding

## SystemVerilog Assertions - Basics and sequences

---

### Introduction to Assertions

#### What is assertions

Assertion is a check against a design specification or rule

> A way to capture a certain specification or rule and then use that as a check in the simulation phase

→ To make sure that the rule is never violated by the design

Example for assertions:
![](note_img\assertion_example.png)

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
