import Erdos883SmallCertificate174Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten174_18 :
    (List.ofFn coreChunks174_18).flatten =
      (coreData174.take (coreResources174 18).q).drop 42 := by
  decide +kernel

theorem coreCheck174_18 :
    ∀ c : Fin 1, (coreChunks174_18 c).all
      (coreResourceRowCheck 159 coreData174 (coreResources174 18)) = true := by
  decide +kernel
#print axioms coreFlatten174_18
#print axioms coreCheck174_18
end Erdos883Verified
