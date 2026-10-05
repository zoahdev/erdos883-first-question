import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_167 :
    (List.ofFn coreChunks999_167).flatten =
      (coreData999.take (coreResources999 167).q).drop 326 := by
  decide +kernel

theorem coreCheck999_167 :
    ∀ c : Fin 1, (coreChunks999_167 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 167)) = true := by
  decide +kernel
#print axioms coreFlatten999_167
#print axioms coreCheck999_167
end Erdos883Verified
