// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Pseudo compressed instruction decoder
 *
 * A pseudo compressed instruction decoder for compressed interface testing.
 *
 */

`include "prim_assert.sv"

module test_pseudo_compressed_decoder  import ibex_pkg::*; (
  input  logic               x_compressed_valid_i,
  output logic               x_compressed_ready_o,
  input  x_compressed_req_t  x_compressed_req_i,
  output x_compressed_resp_t x_compressed_resp_o
);
  // IO signals
  logic [15:0] instr_compressed;
  logic [31:0] instr_decompressed;
  logic        accept;

  // Unused signals
  logic [1:0]            unused_mode;
  logic [X_ID_WIDTH-1:0] unused_id;

  // Connect the signals
  assign instr_compressed = x_compressed_req_i.instr;
  assign unused_mode      = x_compressed_req_i.mode;
  assign unused_id        = x_compressed_req_i.id;

  assign x_compressed_resp_o.instr  = instr_decompressed;
  assign x_compressed_resp_o.accept = accept;

  // Always ready in one cycle
  assign x_compressed_ready_o = x_compressed_valid_i;

  always_comb begin
    instr_decompressed = '0;
    accept             = 1'b0;
    if (x_compressed_valid_i) begin
      if (instr_compressed[1:0] == 2'b01) begin
        if (instr_compressed[15:13] == 3'b000) begin
          // c.addi -> addi rd, rd, nzimm
          // c.nop
          accept             = 1'b1;
          instr_decompressed = {{6 {instr_compressed[12]}}, instr_compressed[12],
                                    instr_compressed[6:2], instr_compressed[11:7], 3'b0,
                                    instr_compressed[11:7], {OPCODE_OP_IMM}};
        end
      end
    end
  end
endmodule
