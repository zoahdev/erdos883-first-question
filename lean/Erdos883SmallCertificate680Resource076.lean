import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_76 :
    (List.ofFn coreChunks680_76).flatten =
      (coreData680.take (coreResources680 76).q).drop 143 := by
  decide +kernel

theorem coreCheck680_76 :
    ∀ c : Fin 1, (coreChunks680_76 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 76)) = true := by
  decide +kernel
#print axioms coreFlatten680_76
#print axioms coreCheck680_76
end Erdos883Verified
