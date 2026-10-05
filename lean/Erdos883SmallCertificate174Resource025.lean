import Erdos883SmallCertificate174Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten174_25 :
    (List.ofFn coreChunks174_25).flatten =
      (coreData174.take (coreResources174 25).q).drop 55 := by
  decide +kernel

theorem coreCheck174_25 :
    ∀ c : Fin 1, (coreChunks174_25 c).all
      (coreResourceRowCheck 159 coreData174 (coreResources174 25)) = true := by
  decide +kernel
#print axioms coreFlatten174_25
#print axioms coreCheck174_25
end Erdos883Verified
