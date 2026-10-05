import Erdos883SmallCertificate174Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten174_19 :
    (List.ofFn coreChunks174_19).flatten =
      (coreData174.take (coreResources174 19).q).drop 43 := by
  decide +kernel

theorem coreCheck174_19 :
    ∀ c : Fin 1, (coreChunks174_19 c).all
      (coreResourceRowCheck 159 coreData174 (coreResources174 19)) = true := by
  decide +kernel
#print axioms coreFlatten174_19
#print axioms coreCheck174_19
end Erdos883Verified
