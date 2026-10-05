import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten158_8 :
    (List.ofFn coreChunks158_8).flatten =
      (coreData158.take (coreResources158 8).q).drop 18 := by
  decide +kernel

theorem coreCheck158_8 :
    ∀ c : Fin 1, (coreChunks158_8 c).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 8)) = true := by
  decide +kernel
#print axioms coreFlatten158_8
#print axioms coreCheck158_8
end Erdos883Verified
