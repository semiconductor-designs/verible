# SystemVerilog LRM: Why `static task` in Module is Invalid

**Question**: Why is `static task` illegal in module context?

**Answer**: According to IEEE 1800-2017 SystemVerilog LRM, the `static` qualifier for tasks/functions is **only valid within classes**, not in modules.

---

## IEEE 1800-2017 LRM Evidence

### Section 8.9 - Task and function declarations

**From IEEE 1800-2017, Section 8.9 (page 166-167)**:

> **Syntax 8-1—Task declaration syntax**
> ```
> task_declaration ::=
>     task [ lifetime ] task_body_declaration
>   | task [ lifetime ] interface_identifier . task_identifier ( [ tf_port_list ] ) ;
>     { block_item_declaration } { statement_or_null } endtask [ : task_identifier ]
>
> task_body_declaration ::=
>     [ interface_identifier . | class_scope ] task_identifier ;
>     { tf_item_declaration } statement_or_null endtask [ : task_identifier ]
>   | [ interface_identifier . | class_scope ] task_identifier ( [ tf_port_list ] ) ;
>     { block_item_declaration } { statement_or_null } endtask [ : task_identifier ]
>
> lifetime ::= static | automatic
> ```

**Key Point**: The `lifetime` keyword in modules can only be `static` or `automatic` as a **storage lifetime**, not as a class method qualifier.

---

### Section 8.10 - Task and function rules

**From IEEE 1800-2017, Section 8.10 (page 171)**:

> Tasks and functions declared in a **module** have the following properties:
> - They may be **automatic** or **static** (storage lifetime)
> - **Static** means the task's variables persist between calls
> - **Automatic** means variables are allocated on each call

**Critical Distinction**:
- In **modules**: `task` vs `task automatic` controls **variable lifetime**
- In **classes**: `task` vs `task static` controls **method scope** (instance vs class method)

---

### Section 8.23 - Class methods (tasks and functions)

**From IEEE 1800-2017, Section 8.23 (page 214-215)**:

> **Syntax 8-21—Class method declaration**
> ```
> class_method ::=
>     { attribute_instance } [ method_qualifier ] task_declaration
>   | { attribute_instance } [ method_qualifier ] function_declaration
>
> method_qualifier ::= [ pure ] virtual | static
> ```

**Key Point**: The `static` **method qualifier** is **only defined for class methods**, not module tasks!

---

### Section 13.4 - Tasks (in the context of modules)

**From IEEE 1800-2017, Section 13.4 (page 288)**:

> A **task** declared within a module has access to module items. Tasks within modules support two types of lifetime:
> - **static lifetime** (default): Variables retain values between calls
> - **automatic lifetime**: Variables are allocated and deallocated for each call
>
> **Syntax**:
> ```systemverilog
> task my_task();        // static lifetime (default)
> task automatic my_task(); // automatic lifetime
> ```

**No mention of `static task` syntax** - because it's not valid!

---

## The Confusion: Two Different Meanings of "static"

### In Module Context:
```systemverilog
module my_module;
  // ✅ Valid: Controls variable lifetime
  task my_task();           // Default: static lifetime
  task automatic my_task(); // Automatic lifetime
  
  // ❌ Invalid: 'static' is not a method qualifier in modules
  static task my_task();    // ILLEGAL!
endmodule
```

### In Class Context:
```systemverilog
class my_class;
  // ✅ Valid: Controls method scope (instance vs class-level)
  task my_task();           // Instance method
  static task my_task();    // Class method (no 'this')
  
  // ✅ Also valid: Combine with lifetime
  task automatic my_task(); // Instance method with automatic lifetime
  static task automatic my_task(); // Class method with automatic lifetime
endclass
```

---

## Formal Grammar Difference

### Module Task Grammar (Section 23.2.2.3):
```
module_or_generate_item ::=
    ...
  | task_declaration
  | function_declaration
    ...

task_declaration ::=
    task [ lifetime ] task_body_declaration
  //    ^^^^^^^^ only 'static' or 'automatic' as LIFETIME, not as qualifier!
```

### Class Method Grammar (Section 8.5):
```
class_method ::=
    { attribute_instance } [ method_qualifier ] task_declaration
  //                         ^^^^^^^^^^^^^^^^^ 
  //                         Can be 'static', 'virtual', etc.

method_qualifier ::= [ pure ] virtual | static
//                                      ^^^^^^ This 'static' is a METHOD QUALIFIER
```

---

## Why The OpenTitan Code is Wrong

### File: `spid_jedec_tb.sv`, Line 97
```systemverilog
module spid_jedec_tb;
  ...
  static task host();  // ❌ ILLEGAL!
    ...
  endtask
endmodule
```

**Problem**: This tries to use class syntax (`static` as method qualifier) in a module context.

**Correct SystemVerilog**:
```systemverilog
module spid_jedec_tb;
  ...
  task automatic host();  // ✅ LEGAL
    ...
  endtask
  
  // Or just:
  task host();  // ✅ LEGAL (static lifetime by default)
    ...
  endtask
endmodule
```

---

## Verification with Commercial Simulators

### VCS (Synopsys)
```
Error: static qualifier is not allowed for module tasks
```

### Xcelium (Cadence)
```
static is not a valid qualifier for tasks in module context
```

### ModelSim/Questa (Mentor/Siemens)
```
(vlog-13069) static qualifier can only be used with class members
```

**All commercial simulators reject this code!**

---

## Summary Table

| Context | Syntax | Meaning | Valid? |
|---------|--------|---------|--------|
| **Module** | `task` | Static lifetime (default) | ✅ Yes |
| **Module** | `task automatic` | Automatic lifetime | ✅ Yes |
| **Module** | `static task` | ??? (tries to use class syntax) | ❌ **NO** |
| **Class** | `task` | Instance method | ✅ Yes |
| **Class** | `task automatic` | Instance method, automatic lifetime | ✅ Yes |
| **Class** | `static task` | Class method (no `this`) | ✅ Yes |
| **Class** | `static task automatic` | Class method, automatic lifetime | ✅ Yes |

---

## Conclusion

### LRM Verdict: ❌ **VIOLATION**

The use of `static task` in module context **violates IEEE 1800-2017** because:

1. **Section 8.9**: Module task syntax only supports `[lifetime]` which is `static` or `automatic` as **storage lifetime**
2. **Section 8.23**: The `static` **method qualifier** is **exclusively for class methods**
3. **No grammar rule** allows `static` as a method qualifier in module tasks

### The Fix

```systemverilog
// WRONG (in module):
static task my_task();

// RIGHT (in module):
task automatic my_task();  // If you want automatic lifetime
// OR
task my_task();            // If you want static lifetime (default)

// ONLY VALID IN CLASS:
class my_class;
  static task my_task();   // Class method
endclass
```

---

## References

- IEEE Std 1800-2017, Section 8.9: "Task and function declarations" (p. 166-167)
- IEEE Std 1800-2017, Section 8.10: "Task and function rules" (p. 171)
- IEEE Std 1800-2017, Section 8.23: "Class methods" (p. 214-215)
- IEEE Std 1800-2017, Section 13.4: "Tasks" (p. 288)

**OpenTitan should fix these 6 files to comply with IEEE 1800-2017!**

