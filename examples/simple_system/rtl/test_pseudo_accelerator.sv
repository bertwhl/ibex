// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Pseudo adder
 *
 * A pseudo accelerator executing addi for testing.
 *
 */

 `include "prim_assert.sv"

module test_pseudo_accelerator import ibex_pkg::*; (
  input  logic                      clk_i,
  input  logic                      rst_ni,
  // Issue Interface
  input  logic                      x_issue_valid_i,
  output logic                      x_issue_ready_o,
  input  x_issue_req_t              x_issue_req_i,
  output x_issue_resp_t             x_issue_resp_o,

  // Commit Interface
  input  logic                      x_commit_valid_i,
  input  x_commit_t                 x_commit_i,

  // Result Interface
  output logic                      x_result_valid_o,
  input  logic                      x_result_ready_i,
  output x_result_t                 x_result_o
);

  opcode_e               opcode;
  logic [2:0]            funct3;
  logic                  accept;
  logic                  ready;
  logic                  commit_valid_new;
  logic                  commit_valid_old;
  logic                  commit_kill;
  logic                  result_receive;
  logic                  reg_en;
  logic [31:0]           rs1_d, rs1_q;
  logic [11:0]           imm_d, imm_q;
  logic [4:0]            rd_d, rd_q;
  logic [X_ID_WIDTH-1:0] id_d, id_q;
  logic [31:0]           adder_in_a;
  logic [31:0]           adder_in_b;
  logic [31:0]           adder_result;
  logic                  commit_new_q;

  assign opcode           = opcode_e'(x_issue_req_i.instr[6:0]);
  assign funct3           = x_issue_req_i.instr[14:12];
  assign accept           = (opcode == OPCODE_OP_IMM) & (funct3 == 3'b000);
  assign ready            = x_issue_valid_i & x_issue_req_i.rs_valid[0];
  assign commit_valid_new = x_commit_valid_i & (x_commit_i.id == id_d);
  assign commit_valid_old = x_commit_valid_i & (x_commit_i.id == id_q);
  assign commit_kill      = x_commit_i.commit_kill;
  assign result_receive   = x_result_ready_i & x_result_valid_o;
  assign rs1_d            = x_issue_req_i.rs[0];
  assign imm_d            = x_issue_req_i.instr[31:20];
  assign rd_d             = x_issue_req_i.instr[11:7];
  assign id_d             = x_issue_req_i.id;
  assign adder_in_a       = rs1_q;
  assign adder_in_b       = { {20{imm_q[11]}}, imm_q };
  assign adder_result     = $unsigned(adder_in_a) + $unsigned(adder_in_b);

  typedef enum logic [1:0] { ACC_IDLE, ACC_WAIT, ACC_RESULT } acc_fsm_e;
  acc_fsm_e acc_fsm_q, acc_fsm_d;

  always_comb begin
    acc_fsm_d        = acc_fsm_q;
    x_issue_ready_o  = 1'b0;
    reg_en           = 1'b0;
    x_result_valid_o = 1'b0;
    unique case (acc_fsm_q)
      ACC_IDLE: begin
        if (ready) begin
          x_issue_ready_o = 1'b1;
          reg_en          = 1'b1;
          if (~accept) begin
            acc_fsm_d = ACC_IDLE;
          end else if (commit_new_q) begin
            acc_fsm_d = ACC_RESULT;
          end else if (~commit_valid_new) begin
            acc_fsm_d = ACC_WAIT;
          end else if (commit_kill) begin
            acc_fsm_d = ACC_IDLE;
          end else if (~commit_kill) begin
            acc_fsm_d = ACC_RESULT;
          end
        end
      end
      ACC_WAIT: begin
        acc_fsm_d = ACC_WAIT;
        if (commit_valid_old & commit_kill) begin
          acc_fsm_d = ACC_IDLE;
        end else if (commit_valid_old & ~commit_kill) begin
          acc_fsm_d = ACC_RESULT;
        end
      end
      ACC_RESULT: begin
        x_result_valid_o = 1'b1;
        if (result_receive) begin
          acc_fsm_d = ACC_IDLE;
        end
      end
      default: acc_fsm_d = ACC_IDLE;
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rs1_q     <= '0;
      imm_q     <= '0;
      rd_q      <= '0;
      id_q      <= '0;
    end else if (reg_en) begin
      rs1_q     <= rs1_d;
      imm_q     <= imm_d;
      rd_q      <= rd_d;
      id_q      <= id_d;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      commit_new_q <= 1'b0;
    end else if (reg_en) begin
      commit_new_q <= 1'b0;
    end else if (commit_valid_new) begin
      commit_new_q <= 1'b1;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      acc_fsm_q <= ACC_IDLE;
    end else begin
      acc_fsm_q <= acc_fsm_d;
    end
  end


  logic [4:0]                           unused_instr;
  priv_lvl_e                            unused_mode;
  logic [X_NUM_RS-2:0][X_RFR_WIDTH-1:0] unused_rs;
  logic [X_NUM_RS-2:0]                  unused_rs_valid;
  logic [5:0]                           unused_ecs;
  logic                                 unused_ecs_valid;

  assign unused_instr     = x_issue_req_i.instr[19:15];
  assign unused_mode      = x_issue_req_i.mode;
  assign unused_rs        = x_issue_req_i.rs[X_NUM_RS-1:1];
  assign unused_rs_valid  = x_issue_req_i.rs_valid[X_NUM_RS-1:1];
  assign unused_ecs       = x_issue_req_i.ecs;
  assign unused_ecs_valid = x_issue_req_i.ecs_valid;

  assign x_issue_resp_o.accept    = accept;
  assign x_issue_resp_o.writeback = 1'b1;
  assign x_issue_resp_o.dualwrite = 1'b0;
  assign x_issue_resp_o.dualread  = 1'b0;
  assign x_issue_resp_o.loadstore = 1'b0;
  assign x_issue_resp_o.ecswrite  = 1'b0;
  assign x_issue_resp_o.exc       = 1'b0;

  assign x_result_o.id      = id_q;
  assign x_result_o.data    = adder_result;
  assign x_result_o.rd      = rd_q;
  assign x_result_o.we      = 1'b1;
  assign x_result_o.ecsdata = '0;
  assign x_result_o.ecswe   = '0;
  assign x_result_o.exc     = 1'b0;
  assign x_result_o.exccode = '0;
  assign x_result_o.dbg     = 1'b0;
  assign x_result_o.err     = 1'b0;

endmodule
