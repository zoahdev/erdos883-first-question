import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_65 :
    (List.ofFn coreChunks680_65).flatten =
      (coreData680.take (coreResources680 65).q).drop 125 := by
  decide +kernel

theorem coreCheck680_65 :
    ∀ c : Fin 1, (coreChunks680_65 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 65)) = true := by
  decide +kernel
#print axioms coreFlatten680_65
#print axioms coreCheck680_65
end Erdos883Verified
