import Erdos883SmallCertificate174Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten174_15 :
    (List.ofFn coreChunks174_15).flatten =
      (coreData174.take (coreResources174 15).q).drop 37 := by
  decide +kernel

theorem coreCheck174_15 :
    ∀ c : Fin 1, (coreChunks174_15 c).all
      (coreResourceRowCheck 159 coreData174 (coreResources174 15)) = true := by
  decide +kernel
#print axioms coreFlatten174_15
#print axioms coreCheck174_15
end Erdos883Verified
