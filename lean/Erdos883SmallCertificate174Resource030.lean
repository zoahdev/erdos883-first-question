import Erdos883SmallCertificate174Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten174_30 :
    (List.ofFn coreChunks174_30).flatten =
      (coreData174.take (coreResources174 30).q).drop 85 := by
  decide +kernel

theorem coreCheck174_30 :
    ∀ c : Fin 1, (coreChunks174_30 c).all
      (coreResourceRowCheck 159 coreData174 (coreResources174 30)) = true := by
  decide +kernel
#print axioms coreFlatten174_30
#print axioms coreCheck174_30
end Erdos883Verified
