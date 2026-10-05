import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_104 :
    (List.ofFn coreChunks999_104).flatten =
      (coreData999.take (coreResources999 104).q).drop 181 := by
  decide +kernel

theorem coreCheck999_104 :
    ∀ c : Fin 1, (coreChunks999_104 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 104)) = true := by
  decide +kernel
#print axioms coreFlatten999_104
#print axioms coreCheck999_104
end Erdos883Verified
