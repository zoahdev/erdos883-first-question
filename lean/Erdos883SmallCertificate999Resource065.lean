import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_65 :
    (List.ofFn coreChunks999_65).flatten =
      (coreData999.take (coreResources999 65).q).drop 245 := by
  decide +kernel

theorem coreCheck999_65 :
    ∀ c : Fin 1, (coreChunks999_65 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 65)) = true := by
  decide +kernel
#print axioms coreFlatten999_65
#print axioms coreCheck999_65
end Erdos883Verified
