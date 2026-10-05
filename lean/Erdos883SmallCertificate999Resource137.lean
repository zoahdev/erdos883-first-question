import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_137 :
    (List.ofFn coreChunks999_137).flatten =
      (coreData999.take (coreResources999 137).q).drop 229 := by
  decide +kernel

theorem coreCheck999_137 :
    ∀ c : Fin 1, (coreChunks999_137 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 137)) = true := by
  decide +kernel
#print axioms coreFlatten999_137
#print axioms coreCheck999_137
end Erdos883Verified
