import Erdos883SmallCertificate174Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten174_36 :
    (List.ofFn coreChunks174_36).flatten =
      (coreData174.take (coreResources174 36).q).drop 49 := by
  decide +kernel

theorem coreCheck174_36 :
    ∀ c : Fin 1, (coreChunks174_36 c).all
      (coreResourceRowCheck 159 coreData174 (coreResources174 36)) = true := by
  decide +kernel
#print axioms coreFlatten174_36
#print axioms coreCheck174_36
end Erdos883Verified
