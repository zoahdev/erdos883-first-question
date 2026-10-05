import Erdos883SmallCertificate174Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten174_1 :
    (List.ofFn coreChunks174_1).flatten =
      (coreData174.take (coreResources174 1).q).drop 19 := by
  decide +kernel

theorem coreCheck174_1 :
    ∀ c : Fin 1, (coreChunks174_1 c).all
      (coreResourceRowCheck 159 coreData174 (coreResources174 1)) = true := by
  decide +kernel
#print axioms coreFlatten174_1
#print axioms coreCheck174_1
end Erdos883Verified
