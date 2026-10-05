import Erdos883SmallCertificate174Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten174_12 :
    (List.ofFn coreChunks174_12).flatten =
      (coreData174.take (coreResources174 12).q).drop 33 := by
  decide +kernel

theorem coreCheck174_12 :
    ∀ c : Fin 1, (coreChunks174_12 c).all
      (coreResourceRowCheck 159 coreData174 (coreResources174 12)) = true := by
  decide +kernel
#print axioms coreFlatten174_12
#print axioms coreCheck174_12
end Erdos883Verified
