import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_76 :
    (List.ofFn coreChunks999_76).flatten =
      (coreData999.take (coreResources999 76).q).drop 139 := by
  decide +kernel

theorem coreCheck999_76 :
    ∀ c : Fin 1, (coreChunks999_76 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 76)) = true := by
  decide +kernel
#print axioms coreFlatten999_76
#print axioms coreCheck999_76
end Erdos883Verified
