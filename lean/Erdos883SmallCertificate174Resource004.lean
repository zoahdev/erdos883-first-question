import Erdos883SmallCertificate174Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten174_4 :
    (List.ofFn coreChunks174_4).flatten =
      (coreData174.take (coreResources174 4).q).drop 42 := by
  decide +kernel

theorem coreCheck174_4 :
    ∀ c : Fin 1, (coreChunks174_4 c).all
      (coreResourceRowCheck 159 coreData174 (coreResources174 4)) = true := by
  decide +kernel
#print axioms coreFlatten174_4
#print axioms coreCheck174_4
end Erdos883Verified
