import Erdos883AdaptiveSpan20682Level6TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength20682_6 : adaptiveNumericSpans20682_6.length = 430 := by decide +kernel
theorem adaptiveSpanEvenCache20682_6 : adaptiveSpanEven20682_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain20682_6 : adaptiveSpanEven20682_6.domainCheck 10341 = true := by decide +kernel
theorem adaptiveSpanEvenEntries20682_6 : adaptiveSpanEven20682_6.spans = coreEvenSpans 10341 0 adaptiveNumericSpans20682_6 := by
  decide +kernel
theorem adaptiveSpanWholeCache20682_6 : adaptiveSpanWhole20682_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain20682_6 : adaptiveSpanWhole20682_6.domainCheck 10341 = true := by decide +kernel
theorem adaptiveSpanWholeEntries20682_6 : adaptiveSpanWhole20682_6.spans = coreWholeSpans 0 adaptiveNumericSpans20682_6 := by
  decide +kernel
end Erdos883Verified
