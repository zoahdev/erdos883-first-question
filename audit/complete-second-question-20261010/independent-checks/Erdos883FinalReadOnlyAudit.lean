import Erdos883SecondCompleteAudit

/-! Independent import-only final-declaration audit. Existing proof files are
read-only for this audit. -/

example : Erdos883Target.FirstQuestion ∧ Erdos883Second.SecondQuestion :=
  Erdos883Verified.erdos883_bothQuestions

set_option pp.explicit true in
#check @Erdos883Verified.erdos883_bothQuestions
set_option pp.explicit true in
#check @Erdos883Verified.erdos883_secondQuestion_raw
#check Erdos883Second.contains_iff_witness
#check Erdos883Second.contains_iff_finsetWitness
#check Erdos883Second.tripartiteVertex_card
#print axioms Erdos883Verified.erdos883_firstQuestion
#print axioms Erdos883Second.farBranch
#print axioms Erdos883Second.secondQuestion
#print axioms Erdos883Verified.erdos883_secondQuestion_raw
#print axioms Erdos883Verified.erdos883_bothQuestions
#print axioms Erdos883Second.contains_iff_witness
#print axioms Erdos883Second.contains_iff_finsetWitness
