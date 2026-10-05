import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten158_29 :
    (List.ofFn coreChunks158_29).flatten =
      (coreData158.take (coreResources158 29).q).drop 65 := by
  decide +kernel

theorem coreCheck158_29 :
    ∀ c : Fin 1, (coreChunks158_29 c).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 29)) = true := by
  decide +kernel
#print axioms coreFlatten158_29
#print axioms coreCheck158_29
end Erdos883Verified
