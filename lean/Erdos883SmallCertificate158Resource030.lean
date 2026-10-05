import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten158_30 :
    (List.ofFn coreChunks158_30).flatten =
      (coreData158.take (coreResources158 30).q).drop 78 := by
  decide +kernel

theorem coreCheck158_30 :
    ∀ c : Fin 1, (coreChunks158_30 c).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 30)) = true := by
  decide +kernel
#print axioms coreFlatten158_30
#print axioms coreCheck158_30
end Erdos883Verified
