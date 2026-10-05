import Erdos883AdaptiveSpan95058Level4TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength95058_4 : adaptiveNumericSpans95058_4.length = 626 := by decide +kernel
theorem adaptiveSpanEvenCache95058_4 : adaptiveSpanEven95058_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain95058_4 : adaptiveSpanEven95058_4.domainCheck 47529 = true := by decide +kernel
theorem adaptiveSpanEvenEntries95058_4 : adaptiveSpanEven95058_4.spans = coreEvenSpans 47529 0 adaptiveNumericSpans95058_4 := by
  decide +kernel
theorem adaptiveSpanWholeCache95058_4 : adaptiveSpanWhole95058_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain95058_4 : adaptiveSpanWhole95058_4.domainCheck 47529 = true := by decide +kernel
theorem adaptiveSpanWholeEntries95058_4 : adaptiveSpanWhole95058_4.spans = coreWholeSpans 0 adaptiveNumericSpans95058_4 := by
  decide +kernel
end Erdos883Verified
