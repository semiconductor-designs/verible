// OpenTitan DV Macros for Verible Parsing
// This file provides macro definitions for DV/UVM code
// Use with: --pre_include=opentitan_dv_macros.svh

// DV utility macros (from dv_macros.svh)
`define DV_CHECK(expr_) \
  if (!(expr_)) begin \
    $error("DV_CHECK failed"); \
  end

`define DV_CHECK_FATAL(expr_) \
  if (!(expr_)) begin \
    $fatal(1, "DV_CHECK_FATAL failed"); \
  end

`define DV_CHECK_EQ(act_, exp_) \
  if ((act_) !== (exp_)) begin \
    $error("DV_CHECK_EQ failed"); \
  end

`define DV_CHECK_EQ_FATAL(act_, exp_) \
  if ((act_) !== (exp_)) begin \
    $fatal(1, "DV_CHECK_EQ_FATAL failed"); \
  end

`define DV_CHECK_NE(act_, exp_) \
  if ((act_) === (exp_)) begin \
    $error("DV_CHECK_NE failed"); \
  end

`define DV_CHECK_NE_FATAL(act_, exp_) \
  if ((act_) === (exp_)) begin \
    $fatal(1, "DV_CHECK_NE_FATAL failed"); \
  end

`define DV_CHECK_LT(act_, exp_) \
  if ((act_) >= (exp_)) begin \
    $error("DV_CHECK_LT failed"); \
  end

`define DV_CHECK_GT(act_, exp_) \
  if ((act_) <= (exp_)) begin \
    $error("DV_CHECK_GT failed"); \
  end

`define DV_CHECK_LE(act_, exp_) \
  if ((act_) > (exp_)) begin \
    $error("DV_CHECK_LE failed"); \
  end

`define DV_CHECK_GE(act_, exp_) \
  if ((act_) < (exp_)) begin \
    $error("DV_CHECK_GE failed"); \
  end

`define DV_CHECK_RANDOMIZE_FATAL(obj_) \
  void'((obj_).randomize())

`define DV_CHECK_RANDOMIZE_WITH_FATAL(obj_, constraints_) \
  void'((obj_).randomize() with constraints_)

// Clock constraint macros
`define DV_COMMON_CLK_CONSTRAINT(freq_) \
  freq_ inside {[1:200]}

// UVM utility macros (empty - just for recognition)
`define uvm_info(id_, msg_, lvl_)
`define uvm_warning(id_, msg_)
`define uvm_error(id_, msg_)
`define uvm_fatal(id_, msg_)
`define gfn get_full_name()

// UVM object macros (empty - just for recognition)
`define uvm_object_utils(T)
`define uvm_component_utils(T)
`define uvm_field_int(ARG, FLAG)
`define uvm_field_object(ARG, FLAG)

