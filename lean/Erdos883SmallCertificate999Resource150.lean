import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_150 :
    (List.ofFn coreChunks999_150).flatten =
      (coreData999.take (coreResources999 150).q).drop 259 := by
  decide +kernel

theorem coreCheck999_150 :
    ∀ c : Fin 1, (coreChunks999_150 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 150)) = true := by
  decide +kernel
#print axioms coreFlatten999_150
#print axioms coreCheck999_150
end Erdos883Verified
