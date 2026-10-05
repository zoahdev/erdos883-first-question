import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_105 :
    (List.ofFn coreChunks999_105).flatten =
      (coreData999.take (coreResources999 105).q).drop 182 := by
  decide +kernel

theorem coreCheck999_105 :
    ∀ c : Fin 1, (coreChunks999_105 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 105)) = true := by
  decide +kernel
#print axioms coreFlatten999_105
#print axioms coreCheck999_105
end Erdos883Verified
