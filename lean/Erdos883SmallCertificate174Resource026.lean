import Erdos883SmallCertificate174Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten174_26 :
    (List.ofFn coreChunks174_26).flatten =
      (coreData174.take (coreResources174 26).q).drop 58 := by
  decide +kernel

theorem coreCheck174_26 :
    ∀ c : Fin 1, (coreChunks174_26 c).all
      (coreResourceRowCheck 159 coreData174 (coreResources174 26)) = true := by
  decide +kernel
#print axioms coreFlatten174_26
#print axioms coreCheck174_26
end Erdos883Verified
