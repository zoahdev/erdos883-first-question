import Erdos883SmallCertificate174Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten174_29 :
    (List.ofFn coreChunks174_29).flatten =
      (coreData174.take (coreResources174 29).q).drop 70 := by
  decide +kernel

theorem coreCheck174_29 :
    ∀ c : Fin 1, (coreChunks174_29 c).all
      (coreResourceRowCheck 159 coreData174 (coreResources174 29)) = true := by
  decide +kernel
#print axioms coreFlatten174_29
#print axioms coreCheck174_29
end Erdos883Verified
