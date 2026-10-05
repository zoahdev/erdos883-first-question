import Erdos883SmallCertificate174Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten174_14 :
    (List.ofFn coreChunks174_14).flatten =
      (coreData174.take (coreResources174 14).q).drop 35 := by
  decide +kernel

theorem coreCheck174_14 :
    ∀ c : Fin 1, (coreChunks174_14 c).all
      (coreResourceRowCheck 159 coreData174 (coreResources174 14)) = true := by
  decide +kernel
#print axioms coreFlatten174_14
#print axioms coreCheck174_14
end Erdos883Verified
