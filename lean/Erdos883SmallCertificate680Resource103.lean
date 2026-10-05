import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_103 :
    (List.ofFn coreChunks680_103).flatten =
      (coreData680.take (coreResources680 103).q).drop 201 := by
  decide +kernel

theorem coreCheck680_103 :
    ∀ c : Fin 1, (coreChunks680_103 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 103)) = true := by
  decide +kernel
#print axioms coreFlatten680_103
#print axioms coreCheck680_103
end Erdos883Verified
