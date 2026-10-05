import Erdos883SmallCertificate174Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten174_16 :
    (List.ofFn coreChunks174_16).flatten =
      (coreData174.take (coreResources174 16).q).drop 39 := by
  decide +kernel

theorem coreCheck174_16 :
    ∀ c : Fin 1, (coreChunks174_16 c).all
      (coreResourceRowCheck 159 coreData174 (coreResources174 16)) = true := by
  decide +kernel
#print axioms coreFlatten174_16
#print axioms coreCheck174_16
end Erdos883Verified
