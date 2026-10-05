import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_44 :
    (List.ofFn coreChunks999_44).flatten =
      (coreData999.take (coreResources999 44).q).drop 210 := by
  decide +kernel

theorem coreCheck999_44 :
    ∀ c : Fin 1, (coreChunks999_44 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 44)) = true := by
  decide +kernel
#print axioms coreFlatten999_44
#print axioms coreCheck999_44
end Erdos883Verified
