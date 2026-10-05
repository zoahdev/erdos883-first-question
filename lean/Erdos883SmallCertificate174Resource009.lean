import Erdos883SmallCertificate174Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten174_9 :
    (List.ofFn coreChunks174_9).flatten =
      (coreData174.take (coreResources174 9).q).drop 29 := by
  decide +kernel

theorem coreCheck174_9 :
    ∀ c : Fin 1, (coreChunks174_9 c).all
      (coreResourceRowCheck 159 coreData174 (coreResources174 9)) = true := by
  decide +kernel
#print axioms coreFlatten174_9
#print axioms coreCheck174_9
end Erdos883Verified
