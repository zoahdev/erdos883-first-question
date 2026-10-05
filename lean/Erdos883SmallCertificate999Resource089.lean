import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_89 :
    (List.ofFn coreChunks999_89).flatten =
      (coreData999.take (coreResources999 89).q).drop 158 := by
  decide +kernel

theorem coreCheck999_89 :
    ∀ c : Fin 1, (coreChunks999_89 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 89)) = true := by
  decide +kernel
#print axioms coreFlatten999_89
#print axioms coreCheck999_89
end Erdos883Verified
