import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_159 :
    (List.ofFn coreChunks999_159).flatten =
      (coreData999.take (coreResources999 159).q).drop 300 := by
  decide +kernel

theorem coreCheck999_159 :
    ∀ c : Fin 1, (coreChunks999_159 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 159)) = true := by
  decide +kernel
#print axioms coreFlatten999_159
#print axioms coreCheck999_159
end Erdos883Verified
