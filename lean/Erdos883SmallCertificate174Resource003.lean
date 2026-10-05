import Erdos883SmallCertificate174Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten174_3 :
    (List.ofFn coreChunks174_3).flatten =
      (coreData174.take (coreResources174 3).q).drop 24 := by
  decide +kernel

theorem coreCheck174_3 :
    ∀ c : Fin 2, (coreChunks174_3 c).all
      (coreResourceRowCheck 159 coreData174 (coreResources174 3)) = true := by
  decide +kernel
#print axioms coreFlatten174_3
#print axioms coreCheck174_3
end Erdos883Verified
