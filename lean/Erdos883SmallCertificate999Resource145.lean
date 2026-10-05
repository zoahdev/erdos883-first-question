import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_145 :
    (List.ofFn coreChunks999_145).flatten =
      (coreData999.take (coreResources999 145).q).drop 251 := by
  decide +kernel

theorem coreCheck999_145 :
    ∀ c : Fin 1, (coreChunks999_145 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 145)) = true := by
  decide +kernel
#print axioms coreFlatten999_145
#print axioms coreCheck999_145
end Erdos883Verified
