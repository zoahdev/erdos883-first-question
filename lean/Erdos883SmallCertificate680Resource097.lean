import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_97 :
    (List.ofFn coreChunks680_97).flatten =
      (coreData680.take (coreResources680 97).q).drop 177 := by
  decide +kernel

theorem coreCheck680_97 :
    ∀ c : Fin 1, (coreChunks680_97 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 97)) = true := by
  decide +kernel
#print axioms coreFlatten680_97
#print axioms coreCheck680_97
end Erdos883Verified
