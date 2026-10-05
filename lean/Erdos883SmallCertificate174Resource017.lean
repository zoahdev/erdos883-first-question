import Erdos883SmallCertificate174Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten174_17 :
    (List.ofFn coreChunks174_17).flatten =
      (coreData174.take (coreResources174 17).q).drop 41 := by
  decide +kernel

theorem coreCheck174_17 :
    ∀ c : Fin 1, (coreChunks174_17 c).all
      (coreResourceRowCheck 159 coreData174 (coreResources174 17)) = true := by
  decide +kernel
#print axioms coreFlatten174_17
#print axioms coreCheck174_17
end Erdos883Verified
