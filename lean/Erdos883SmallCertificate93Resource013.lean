import Erdos883SmallCertificate93Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten93_13 :
    (List.ofFn coreChunks93_13).flatten =
      (coreData93.take (coreResources93 13).q).drop 31 := by
  decide +kernel

theorem coreCheck93_13 :
    ∀ c : Fin 1, (coreChunks93_13 c).all
      (coreResourceRowCheck 93 coreData93 (coreResources93 13)) = true := by
  decide +kernel
#print axioms coreFlatten93_13
#print axioms coreCheck93_13
end Erdos883Verified
