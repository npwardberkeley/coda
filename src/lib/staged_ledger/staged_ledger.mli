module Make (Inputs : Coda_intf.Tmp_test_stub_hack.For_staged_ledger_intf) :
  Coda_intf.Staged_ledger_generalized_intf
  with type diff := Inputs.Staged_ledger_diff.t
   and type valid_diff :=
              Inputs.Staged_ledger_diff.With_valid_signatures_and_proofs.t
   and type ledger_proof := Inputs.Ledger_proof.t
   and type verifier := Inputs.Verifier.t
   and type transaction_snark_work := Inputs.Transaction_snark_work.t
   and type transaction_snark_work_statement :=
              Inputs.Transaction_snark_work.Statement.t
   and type transaction_snark_work_checked :=
              Inputs.Transaction_snark_work.Checked.t
   and type compressed_public_key := Inputs.Compressed_public_key.t
   and type ledger_hash := Inputs.Ledger_hash.t
   and type frozen_ledger_hash := Inputs.Frozen_ledger_hash.t
   and type staged_ledger_hash := Inputs.Staged_ledger_hash.t
   and type staged_ledger_aux_hash := Inputs.Staged_ledger_aux_hash.t
   and type pending_coinbase := Inputs.Pending_coinbase.t
   and type ledger := Inputs.Ledger.t
   and type user_command := Inputs.User_command.t
   and type user_command_with_valid_signature :=
              Inputs.User_command.With_valid_signature.t
   and type transaction := Inputs.Transaction.t
   and type transaction_witness := Inputs.Transaction_witness.t
   and type transaction_snark_statement := Inputs.Transaction_snark_statement.t

include
  Coda_intf.Staged_ledger_intf
  with type diff := Staged_ledger_diff.t
   and type valid_diff := Staged_ledger_diff.With_valid_signatures_and_proofs.t
   and type ledger_proof := Ledger_proof.t
   and type transaction_snark_work := Transaction_snark_work.t
   and type transaction_snark_work_statement :=
              Transaction_snark_work.Statement.t
   and type transaction_snark_work_checked := Transaction_snark_work.Checked.t
   and type verifier := Verifier.t
