import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten158_20 :
    (List.ofFn coreChunks158_20).flatten =
      (coreData158.take (coreResources158 20).q).drop 39 := by
  decide +kernel

theorem coreCheck158_20 :
    ∀ c : Fin 1, (coreChunks158_20 c).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 20)) = true := by
  decide +kernel
#print axioms coreFlatten158_20
#print axioms coreCheck158_20
end Erdos883Verified
