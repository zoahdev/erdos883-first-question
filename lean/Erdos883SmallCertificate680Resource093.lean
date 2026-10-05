import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_93 :
    (List.ofFn coreChunks680_93).flatten =
      (coreData680.take (coreResources680 93).q).drop 173 := by
  decide +kernel

theorem coreCheck680_93 :
    ∀ c : Fin 1, (coreChunks680_93 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 93)) = true := by
  decide +kernel
#print axioms coreFlatten680_93
#print axioms coreCheck680_93
end Erdos883Verified
