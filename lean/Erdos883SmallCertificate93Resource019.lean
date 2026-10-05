import Erdos883SmallCertificate93Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten93_19 :
    (List.ofFn coreChunks93_19).flatten =
      (coreData93.take (coreResources93 19).q).drop 30 := by
  decide +kernel

theorem coreCheck93_19 :
    ∀ c : Fin 1, (coreChunks93_19 c).all
      (coreResourceRowCheck 93 coreData93 (coreResources93 19)) = true := by
  decide +kernel
#print axioms coreFlatten93_19
#print axioms coreCheck93_19
end Erdos883Verified
