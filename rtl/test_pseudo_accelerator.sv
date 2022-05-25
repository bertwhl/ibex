// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0


/**
 * Pseudo load and store accelerator
 *
 * A pseudo accelerator executing load and store for testing.
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

  // Memory Interface
  output logic                      x_mem_valid_o,
  input  logic                      x_mem_ready_i,
  output x_mem_req_t                x_mem_req_o,
  input  x_mem_resp_t               x_mem_resp_i,

  // Memory Result Interface
  input  logic                      x_mem_result_valid_i,
  input  x_mem_result_t             x_mem_result_i,

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

  logic                  accept_ready;
  logic                  commit_vnew;
  logic                  commit_vold;
  logic                  commit_kill;
  logic                  insn_valid;
  logic                  x_issue_accept;
  logic                  reg_en;
  logic                  data_en;

  logic                  commit_d, commit_q;
  logic [X_ID_WIDTH-1:0] id_d, id_q;
  logic                  we_d, we_q;
  priv_lvl_e             mode_d, mode_q;
  logic [1:0]            size_d, size_q;
  logic                  sign_d, sign_q;
  logic [31:0]           addr_d, addr_q;
  logic [31:0]           data_d, data_q;
  logic [4:0]            rd_d, rd_q;
  logic [31:0]           addr_base;
  logic [31:0]           addr_offset;
  logic [31:0]           rdata;


  assign opcode = opcode_e'(x_issue_req_i.instr[6:0]);
  assign funct3 = x_issue_req_i.instr[14:12];

  assign commit_vnew = x_commit_valid_i & (x_commit_i.id == id_d);
  assign commit_vold = x_commit_valid_i & (x_commit_i.id == id_q);
  assign commit_kill = x_commit_i.commit_kill;

  assign id_d   = x_issue_req_i.id;
  assign rd_d   = x_issue_req_i.instr[11:7];
  assign mode_d = x_issue_req_i.mode;
  assign size_d = funct3[1:0];
  assign sign_d = ~funct3[2];

  assign addr_base = x_issue_req_i.rs[0];
  assign addr_offset[31:12] = {20{x_issue_req_i.instr[31]}};
  assign addr_offset[11:5]  = x_issue_req_i.instr[31:25];
  assign addr_offset[4:0]   = we_d ? x_issue_req_i.instr[11:7] : x_issue_req_i.instr[24:20];
  assign addr_d = $unsigned(addr_base) + $unsigned(addr_offset);

  assign accept_ready = x_issue_req_i.rs_valid[0] & (~we_d | x_issue_req_i.rs_valid[1]);
  assign reg_en = x_issue_valid_i & x_issue_ready_o;

  logic sign_bits;

  always_comb begin
    unique case (size_q)
      2'b00: begin
        sign_bits = sign_q & x_mem_result_i.rdata[7];
        rdata = {{24{sign_bits}}, x_mem_result_i.rdata[7:0]};
      end
      2'b01: begin
        sign_bits = sign_q & x_mem_result_i.rdata[15];
        rdata = {{16{sign_bits}}, x_mem_result_i.rdata[15:0]};
      end
      2'b10: rdata = x_mem_result_i.rdata;
      default:;
    endcase
  end

  always_comb begin
    insn_valid = 1'b0;
    we_d       = 1'b0;
    unique case (opcode)
      OPCODE_STORE: begin
        unique case (funct3)
          3'b000, // sb
          3'b001, // sh
          3'b010: begin // sw
            insn_valid = 1'b1;
            we_d  = 1'b1;
          end
          default:;
        endcase
      end
      OPCODE_LOAD: begin
        unique case (funct3)
          3'b000, // lb
          3'b001, // lh
          3'b010, // lw
          3'b100, // lbu
          3'b101: begin // lhu
            insn_valid = 1'b1;
            we_d       = 1'b0;
          end
          default:;
        endcase
      end
      default: ;
    endcase
  end

  typedef enum logic [1:0] { ACC_IDLE, ACC_MEM, ACC_MEM_WAIT, ACC_RESULT } acc_fsm_e;
  acc_fsm_e acc_fsm_q, acc_fsm_d;

  always_comb begin
    acc_fsm_d        = acc_fsm_q;
    commit_d         = commit_q;
    data_d           = '0;
    data_en          = 1'b0;
    x_issue_ready_o  = 1'b0;
    x_issue_accept   = 1'b0;
    x_mem_valid_o    = 1'b0;
    x_result_valid_o = 1'b0;
    unique case (acc_fsm_q)
      ACC_IDLE: begin
        if (x_issue_valid_i) begin
          if (~insn_valid) begin
            x_issue_ready_o = 1'b1;
            x_issue_accept  = 1'b0;
            acc_fsm_d = ACC_IDLE;
          end else if (accept_ready) begin
            x_issue_ready_o = 1'b1;
            x_issue_accept  = 1'b1;
            data_d          = x_issue_req_i.rs[1];
            data_en         = we_d;
            if (~commit_vnew) begin
              acc_fsm_d = ACC_MEM;
            end else if (commit_kill) begin
              acc_fsm_d = ACC_IDLE;
            end else begin
              acc_fsm_d = ACC_MEM;
              commit_d  = 1'b1;
            end
          end
        end
      end
      ACC_MEM: begin
        x_mem_valid_o = 1'b1;
        if (commit_vold & commit_kill) begin
          acc_fsm_d = ACC_IDLE;
        end else if (x_mem_ready_i) begin
          acc_fsm_d = ACC_MEM_WAIT;
        end
        if (commit_vold & ~commit_kill) begin
          commit_d  = 1'b1;
        end
      end
      ACC_MEM_WAIT: begin
        if (x_mem_result_valid_i & (x_mem_result_i.id == id_q)) begin
          acc_fsm_d = ACC_RESULT;
          data_d    = rdata;
          data_en   = ~we_q;
        end
      end
      ACC_RESULT: begin
        x_result_valid_o = 1'b1;
        if (x_result_ready_i) begin
          acc_fsm_d = ACC_IDLE;
          commit_d  = 1'b0;
        end
      end
      default: acc_fsm_d = ACC_IDLE;
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      id_q   <= '0;
      we_q   <= '0;
      mode_q <= '0;
      size_q <= '0;
      sign_q <= '0;
      addr_q <= '0;
      rd_q   <= '0;
    end else if (reg_en) begin
      id_q   <= id_d;
      we_q   <= we_d;
      mode_q <= mode_d;
      size_q <= size_d;
      sign_q <= sign_d;
      addr_q <= addr_d;
      rd_q   <= rd_d;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      data_q <= '0;
    end else if (data_en) begin
      data_q <= data_d;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      commit_q  <= '0;
      acc_fsm_q <= ACC_IDLE;
    end else begin
      commit_q  <= commit_d;
      acc_fsm_q <= acc_fsm_d;
    end
  end

  logic [4:0]  unused_issue_req_instr;
  logic [5:0]  unused_issue_req_ecs;
  logic        unused_issue_req_ecs_valid;
  x_mem_resp_t unused_mem_resp;
  logic        unused_mem_result_err;
  logic        unused_mem_result_dbg;

  assign unused_issue_req_instr     = x_issue_req_i.instr[19:15];
  assign unused_issue_req_ecs       = x_issue_req_i.ecs;
  assign unused_issue_req_ecs_valid = x_issue_req_i.ecs_valid;

  if (X_NUM_RS == 3) begin
    logic [X_RFR_WIDTH-1:0] unused_rs;
    logic                   unused_rs_valid;
    assign unused_rs       = x_issue_req_i.rs[2];
    assign unused_rs_valid = x_issue_req_i.rs_valid[2];
  end

  assign x_issue_resp_o.accept    = x_issue_accept;
  assign x_issue_resp_o.writeback = ~we_d;
  assign x_issue_resp_o.dualwrite = 1'b0;
  assign x_issue_resp_o.dualread  = 1'b0;
  assign x_issue_resp_o.loadstore = 1'b1;
  assign x_issue_resp_o.ecswrite  = 1'b0;
  assign x_issue_resp_o.exc       = 1'b0;

  assign x_mem_req_o.id    = id_q;
  assign x_mem_req_o.addr  = addr_q;
  assign x_mem_req_o.mode  = mode_q;
  assign x_mem_req_o.we    = we_q;
  assign x_mem_req_o.size  = {1'b0, size_q};
  assign x_mem_req_o.be    = 4'b1111;
  assign x_mem_req_o.attr  = '0;
  assign x_mem_req_o.wdata = data_q;
  assign x_mem_req_o.last  = 1'b1;
  assign x_mem_req_o.spec  = ~commit_q;

  assign unused_mem_resp = x_mem_resp_i;

  assign unused_mem_result_err = x_mem_result_i.err;
  assign unused_mem_result_dbg = x_mem_result_i.dbg;

  assign x_result_o.id      = id_q;
  assign x_result_o.data    = data_q;
  assign x_result_o.rd      = rd_q;
  assign x_result_o.we      = ~we_q;
  assign x_result_o.ecsdata = '0;
  assign x_result_o.ecswe   = '0;
  assign x_result_o.exc     = 1'b0;
  assign x_result_o.exccode = '0;
  assign x_result_o.dbg     = 1'b0;
  assign x_result_o.err     = 1'b0;

endmodule
