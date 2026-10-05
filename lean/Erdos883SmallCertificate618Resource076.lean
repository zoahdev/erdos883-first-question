import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_76 :
    (List.ofFn coreChunks618_76).flatten =
      (coreData618.take (coreResources618 76).q).drop 151 := by
  decide +kernel

theorem coreCheck618_76 :
    ∀ c : Fin 1, (coreChunks618_76 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 76)) = true := by
  decide +kernel
#print axioms coreFlatten618_76
#print axioms coreCheck618_76
end Erdos883Verified
