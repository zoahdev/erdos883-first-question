import Erdos883AdaptiveSpan95058Level1TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength95058_1 : adaptiveNumericSpans95058_1.length = 626 := by decide +kernel
theorem adaptiveSpanEvenCache95058_1 : adaptiveSpanEven95058_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain95058_1 : adaptiveSpanEven95058_1.domainCheck 47529 = true := by decide +kernel
theorem adaptiveSpanEvenEntries95058_1 : adaptiveSpanEven95058_1.spans = coreEvenSpans 47529 0 adaptiveNumericSpans95058_1 := by
  decide +kernel
theorem adaptiveSpanWholeCache95058_1 : adaptiveSpanWhole95058_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain95058_1 : adaptiveSpanWhole95058_1.domainCheck 47529 = true := by decide +kernel
theorem adaptiveSpanWholeEntries95058_1 : adaptiveSpanWhole95058_1.spans = coreWholeSpans 0 adaptiveNumericSpans95058_1 := by
  decide +kernel
end Erdos883Verified
