import Erdos883SmallCertificate174Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten174_10 :
    (List.ofFn coreChunks174_10).flatten =
      (coreData174.take (coreResources174 10).q).drop 30 := by
  decide +kernel

theorem coreCheck174_10 :
    ∀ c : Fin 1, (coreChunks174_10 c).all
      (coreResourceRowCheck 159 coreData174 (coreResources174 10)) = true := by
  decide +kernel
#print axioms coreFlatten174_10
#print axioms coreCheck174_10
end Erdos883Verified
