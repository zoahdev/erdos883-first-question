import Erdos883SmallCertificate174Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten174_28 :
    (List.ofFn coreChunks174_28).flatten =
      (coreData174.take (coreResources174 28).q).drop 66 := by
  decide +kernel

theorem coreCheck174_28 :
    ∀ c : Fin 1, (coreChunks174_28 c).all
      (coreResourceRowCheck 159 coreData174 (coreResources174 28)) = true := by
  decide +kernel
#print axioms coreFlatten174_28
#print axioms coreCheck174_28
end Erdos883Verified
