import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_65 :
    (List.ofFn coreChunks618_65).flatten =
      (coreData618.take (coreResources618 65).q).drop 132 := by
  decide +kernel

theorem coreCheck618_65 :
    ∀ c : Fin 1, (coreChunks618_65 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 65)) = true := by
  decide +kernel
#print axioms coreFlatten618_65
#print axioms coreCheck618_65
end Erdos883Verified
